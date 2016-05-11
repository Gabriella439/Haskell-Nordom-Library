{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecursiveDo        #-}

-- | Parsing logic for the Morte language

module Nordom.Parser (
    -- * Parser
    exprFromText,

    -- * Errors
    ParseError(..),
    ParseMessage(..)
    ) where

import Nordom.Core
import Nordom.Lexer (Position, Token, LocatedToken(..))
import Control.Applicative hiding (Const)
import Control.Exception (Exception)
import Control.Monad.Trans.Class  (lift)
import Control.Monad.Trans.Except (Except, throwE, runExceptT)
import Control.Monad.Trans.State.Strict (evalState, get)
import Data.Monoid
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Typeable (Typeable)
import Filesystem.Path.CurrentOS (FilePath)
import Prelude hiding (FilePath)
import Text.Earley

import qualified Nordom.Lexer   as Lexer
import qualified Pipes.Prelude  as Pipes
import qualified Data.Text.Lazy as Text
import qualified Data.Vector    as Vector

match :: Token -> Prod r Token LocatedToken Token
match t = fmap Lexer.token (satisfy predicate) <?> t
  where
    predicate (LocatedToken t' _) = t == t'

label :: Prod r e LocatedToken Text
label = fmap unsafeFromLabel (satisfy isLabel)
  where
    isLabel (LocatedToken (Lexer.Label _) _) = True
    isLabel  _                               = False

    unsafeFromLabel (LocatedToken (Lexer.Label l) _) = l

number :: Prod r e LocatedToken Int
number = fmap unsafeFromNumber (satisfy isNumber)
  where
    isNumber (LocatedToken (Lexer.Number _) _) = True
    isNumber  _                                = False

    unsafeFromNumber (LocatedToken (Lexer.Number n) _) = n

file :: Prod r e LocatedToken FilePath
file = fmap unsafeFromFile (satisfy isFile)
  where
    isFile (LocatedToken (Lexer.File _) _) = True
    isFile  _                              = False

    unsafeFromFile (LocatedToken (Lexer.File n) _) = n

url :: Prod r e LocatedToken Text
url = fmap unsafeFromURL (satisfy isURL)
  where
    isURL (LocatedToken (Lexer.URL _) _) = True
    isURL  _                             = False

    unsafeFromURL (LocatedToken (Lexer.URL n) _) = n

sepBy1 :: Alternative f => f a -> f b -> f [a]
sepBy1 x sep = (:) <$> x <*> many (sep *> x)

sepBy :: Alternative f => f a -> f b -> f [a]
sepBy x sep = sepBy1 x sep <|> pure []

expr :: Grammar r (Prod r Token LocatedToken (Expr Path))
expr = mdo
    expr <- rule
        (   bexpr
        <|>     Lam
            <$> (match Lexer.Lambda *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr)
        <|>     Pi
            <$> (match Lexer.Pi *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr)
        <|> Pi "_" <$> bexpr <*> (match Lexer.Arrow *> expr)
        )

    vexpr <- rule
        (   V <$> label <*> (match Lexer.At *> number)
        <|> V <$> label <*> pure 0
        )

    bexpr <- rule
        (   App <$> bexpr <*> aexpr
        <|> aexpr
        )

    aexpr <- rule
        (   Var <$> vexpr
        <|> match Lexer.Star *> pure (Const Star)
        <|> match Lexer.Box  *> pure (Const Box )
        <|> Embed <$> embed
        <|> (NatLit . fromIntegral) <$> number
        <|>     ListLit
            <$> (match Lexer.OpenList *> expr)
            <*> (fmap Vector.fromList (many (match Lexer.Comma *> expr)) <* match Lexer.CloseBracket)
        <|>     PathLit
            <$> (match Lexer.OpenPath *> expr)
            <*> many ((,) <$> object <*> expr)
            <*> (object <* match Lexer.CloseBracket)
        <|>     Do
            <$> (match Lexer.Do *> expr)
            <*> (match Lexer.OpenBrace *> many bind)
            <*> (bind <* match Lexer.CloseBrace)
        <|> match Lexer.Nat        *> pure Nat
        <|> match Lexer.NatPlus    *> pure NatPlus
        <|> match Lexer.NatTimes   *> pure NatTimes
        <|> match Lexer.List       *> pure List
        <|> match Lexer.ListAppend *> pure ListAppend
        <|> match Lexer.ListEnum   *> pure ListEnum
        <|> match Lexer.ListFold   *> pure ListFold
        <|> match Lexer.ListHead   *> pure ListHead
        <|> match Lexer.ListLength *> pure ListLength
        <|> match Lexer.ListMap    *> pure ListMap
        <|> match Lexer.Cmd        *> pure Cmd
        <|> match Lexer.Path       *> pure Path
        <|> (match Lexer.OpenParen *> expr <* match Lexer.CloseParen)
        )

    arg <- rule
        (       Arg
            <$> (match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr <* match Lexer.CloseParen)
        <|>     Arg "_" <$> aexpr
        )

    args <- rule (many arg)

    object <- rule (match Lexer.OpenBrace *> expr <* match Lexer.CloseBrace)

    bind <- rule
        (   (\x y z -> Bind (Arg x y) z)
        <$> label
        <*> (match Lexer.Colon *> expr)
        <*> (match Lexer.LArrow *> expr <* match Lexer.Semicolon)
        )

    embed <- rule
        (   File <$> file
        <|> URL <$> url
        )

    return expr

-- | The specific parsing error
data ParseMessage
    -- | Lexing failed, returning the remainder of the text
    = Lexing Text
    -- | Parsing failed, returning the invalid token and the expected tokens
    | Parsing Token [Token]
    deriving (Show)

-- | Structured type for parsing errors
data ParseError = ParseError
    { position     :: Position
    , parseMessage :: ParseMessage
    } deriving (Typeable)

instance Show ParseError where
    show = Text.unpack . toLazyText . build

instance Exception ParseError

instance Buildable ParseError where
    build (ParseError (Lexer.P l c) e) =
            "\n"
        <>  "Line:   " <> build l <> "\n"
        <>  "Column: " <> build c <> "\n"
        <>  "\n"
        <>  case e of
            Lexing r                                     ->
                    "Lexing: \"" <> build remainder <> dots <> "\"\n"
                <>  "\n"
                <>  "Error: Lexing failed\n"
              where
                remainder = Text.takeWhile (/= '\n') (Text.take 64 r)
                dots      = if Text.length r > 64 then "..." else mempty
            Parsing t ts ->
                    "Parsing : " <> build (show t ) <> "\n"
                <>  "Expected: " <> build (show ts) <> "\n"
                <>  "\n"
                <>  "Error: Parsing failed\n"

runParser
    :: (forall r . Grammar r (Prod r Token LocatedToken a))
    -> Text
    -> Either ParseError a
runParser p text = evalState (runExceptT m) (Lexer.P 1 0)
  where
    m = do
        (locatedTokens, mtxt) <- lift (Pipes.toListM' (Lexer.lexExpr text))
        case mtxt of
            Nothing  -> return ()
            Just txt -> do
                pos <- lift get
                throwE (ParseError pos (Lexing txt))
        let (parses, Report _ needed found) =
                fullParses (parser p) locatedTokens
        case parses of
            parse:_ -> return parse
            []      -> do
                let LocatedToken t pos = case found of
                        lt:_ -> lt
                        _    -> LocatedToken Lexer.EOF (Lexer.P 0 0)
                throwE (ParseError pos (Parsing t needed))

-- | Parse an `Expr` from `Text` or return a `ParseError` if parsing fails
exprFromText :: Text -> Either ParseError (Expr Path)
exprFromText = runParser expr
