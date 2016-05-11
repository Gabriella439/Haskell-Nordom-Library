{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# OPTIONS_GHC -Wall #-}

module Nordom.Core (
    -- * Syntax
    Var(..),
    Const(..),
    Path(..),
    X(..),
    Arg(..),
    Bind(..),
    Expr(..),
    Context,

    -- * Core functions
    typeWith,
    typeOf,
    normalize,

    -- * Utilities
    shift,
    subst,
    pretty,

    -- * Errors
    TypeError(..),
    TypeMessage(..),
    ) where

import Control.Applicative (pure, empty)
import Control.Exception (Exception)
import Data.Monoid ((<>))
import Data.String (IsString(..))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Data.Typeable (Typeable)
import Data.Vector (Vector)
import Filesystem.Path (FilePath)
import Nordom.Context (Context)
import Prelude hiding (FilePath, pi)

import qualified Control.Monad.Trans.State as State
import qualified Data.Text.Lazy            as Text
import qualified Data.Text.Lazy.Builder    as Builder
import qualified Data.Vector               as Vector
import qualified Filesystem.Path.CurrentOS as Filesystem
import qualified Nordom.Context            as Context

{-| Label for a bound variable

    The `Text` field is the variable's name (i.e. \"@x@\").

    The `Int` field disambiguates variables with the same name if there are
    multiple bound variables of the same name in scope.  Zero refers to the
    nearest bound variable and the index increases by one for each bound variable
    of the same name going outward.  The following diagram may help:

>                           +-refers to-+
>                           |           |
>                           v           |
> \(x : *) -> \(y : *) -> \(x : *) -> x@0
>
>   +-------------refers to-------------+
>   |                                   |
>   v                                   |
> \(x : *) -> \(y : *) -> \(x : *) -> x@1

    This `Int` behaves like a De Bruijn index in the special case where all
    variables have the same name.

    You can optionally omit the index if it is @0@:

>                           +refers to+
>                           |         |
>                           v         |
> \(x : *) -> \(y : *) -> \(x : *) -> x

    Zero indices are omitted when pretty-printing `Var`s and non-zero indices
    appear as a numeric suffix.
-}
data Var = V Text Int deriving (Eq, Show)

instance IsString Var
  where
    fromString str = V (Text.pack str) 0

instance Buildable Var where
    build (V txt n) = build txt <> if n == 0 then "" else ("@" <> build n)

{-| Constants for the calculus of constructions

    The only axiom is:

> ⊦ * : □

    ... and all four rule pairs are valid:

> ⊦ * ↝ * : *
> ⊦ □ ↝ * : *
> ⊦ * ↝ □ : □
> ⊦ □ ↝ □ : □

-}
data Const = Star | Box deriving (Eq, Show, Bounded, Enum)

instance Buildable Const where
    build c = case c of
        Star -> "*"
        Box  -> "□"

axiom :: Const -> Either TypeError Const
axiom Star = return Box
axiom Box  = Left (TypeError Context.empty (Const Box) (Untyped Box))

rule :: Const -> Const -> Either TypeError Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Path to an external resource
data Path
    = File FilePath
    | URL  Text
    deriving (Eq, Ord, Show)

instance Buildable Path where
    build (File file)
        |  Text.isPrefixOf  "./" txt
        || Text.isPrefixOf   "/" txt
        || Text.isPrefixOf "../" txt
        = build txt <> " "
        | otherwise
        = "./" <> build txt <> " "
      where
        txt = Text.fromStrict (either id id (Filesystem.toText file))
    build (URL  str ) = build str <> " "

-- | Like `Data.Void.Void`, but with a `Buildable` instance
newtype X = X { absurd :: forall a . a }

instance Eq X where
    _ == _ = True

instance Show X where
    show = absurd

instance Buildable X where
    build = absurd

{-| Argument for function or constructor definitions

> Arg "_" _A  ~       _A
> Arg  x  _A  ~  (x : _A)
-}
data Arg a = Arg
    { argName :: Text
    , argType :: Expr a
    } deriving (Functor, Foldable, Traversable, Show)

instance Buildable a => Buildable (Arg a) where
    build (Arg x _A) = build x <> " : " <> build _A

{-|
> Bind arg e  ~  arg <- e;
-}
data Bind a = Bind
    { bindLhs :: Arg a
    , bindRhs :: Expr a
    } deriving (Functor, Foldable, Traversable, Show)

instance Buildable a => Buildable (Bind a) where
    build (Bind l r) = build l <> " <- " <> build r <> ";"

-- | Syntax tree for expressions
data Expr a
    -- | > Const c                         ~  c
    = Const Const
    -- | > Var (V x 0)                     ~  x
    --   > Var (V x n)                     ~  x@n
    | Var Var
    -- | > Lam x     _A  b                 ~  λ(x : _A) →  b
    | Lam Text (Expr a) (Expr a)
    -- | > Pi x      _A _B                 ~  ∀(x : _A) → _B
    | Pi  Text (Expr a) (Expr a)
    -- | > App f a                         ~  f a
    | App (Expr a) (Expr a)
    -- | > NatLit  n                       ~  n
    | NatLit !Integer
    -- | > Nat                             ~  #Nat
    | Nat
    -- | > NatPlus                         ~  #Nat/(+)
    | NatPlus
    -- | > NatTimes                        ~  #Nat/(*)
    | NatTimes
    -- | > ListLit t [x, y, z]             ~  [nil t,x,y,z]
    | ListLit (Expr a) (Vector (Expr a))
    -- | > List                            ~  #List
    | List
    -- | > ListAppend                      ~  #List/append
    | ListAppend
    -- | > ListEnum                        ~  #List/enum
    | ListEnum
    -- | > ListFold                        ~  #List/fold
    | ListFold
    -- | > ListMap                         ~  #List/map
    | ListMap
    -- | > PathLit c [(o1, m1), (o2, m2)] o3  ~  [id c {o1} m1 {o2} m2 {o3}]
    | PathLit (Expr a) [(Expr a, Expr a)] (Expr a)
    -- | > Path                            ~  #Path
    | Path
    -- | > Do m [b1, b2] b3                ~  do m { b1 b2 b3 }
    | Do (Expr a) [Bind a] (Bind a)
    -- | > Cmd                             ~  #Cmd
    | Cmd
    | Embed a
    deriving (Functor, Foldable, Traversable, Show)

instance Applicative Expr where
    pure = Embed

    mf <*> mx = case mf of
        Const c           -> Const c
        Var   v           -> Var v
        Lam x _A  b       -> Lam x (_A <*> mx) ( b <*> mx)
        Pi  x _A _B       -> Pi  x (_A <*> mx) (_B <*> mx)
        App f a           -> App (f <*> mx) (a <*> mx)
        NatLit n          -> NatLit n
        Nat               -> Nat
        NatPlus           -> NatPlus
        NatTimes          -> NatTimes
        ListLit t es      -> ListLit (t <*> mx) es'
          where
            es' = do
                e <- es
                return (e <*> mx)
        List              -> List
        ListAppend        -> ListAppend
        ListEnum          -> ListEnum
        ListFold          -> ListFold
        ListMap           -> ListMap
        PathLit cat ps o0 -> PathLit (cat <*> mx) ps' (o0 <*> mx)
          where
            ps' = do
                (o, m) <- ps
                return (o <*> mx, m <*> mx)
        Path              -> Path
        Do m bs b0        -> Do (m <*> mx) bs' b0'
          where
            bs' = do
                Bind (Arg x _A) r <- bs
                return (Bind (Arg x (_A <*> mx)) (r <*> mx))
            Bind (Arg x0 _A0) r0 = b0
            b0' = Bind (Arg x0 (_A0 <*> mx)) (r0 <*> mx)
        Cmd               -> Cmd
        Embed f           -> fmap f mx

instance Monad Expr where
    return = Embed

    m >>= k = case m of
        Const c           -> Const c
        Var   v           -> Var v
        Lam x _A  b       -> Lam x (_A >>= k) ( b >>= k)
        Pi  x _A _B       -> Pi  x (_A >>= k) (_B >>= k)
        App f a           -> App (f >>= k) (a >>= k)
        NatLit n          -> NatLit n
        Nat               -> Nat
        NatPlus           -> NatPlus
        NatTimes          -> NatTimes
        ListLit t es      -> ListLit (t >>= k) es'
          where
            es' = do
                e <- es
                return (e >>= k)
        List              -> List
        ListAppend        -> ListAppend
        ListEnum          -> ListEnum
        ListFold          -> ListFold
        ListMap           -> ListMap
        PathLit cat ps o0 -> PathLit (cat >>= k) ps' (o0 >>= k)
          where
            ps' = do
                (o, m_) <- ps
                return (o >>= k, m_ >>= k)
        Path              -> Path
        Do m_ bs b0       -> Do (m_ >>= k) bs' b0'
          where
            bs' = do
                Bind (Arg x _A) r <- bs
                return (Bind (Arg x (_A >>= k)) (r >>= k))
            Bind (Arg x0 _A0) r0 = b0
            b0' = Bind (Arg x0 (_A0 >>= k)) (r0 >>= k)
        Cmd               -> Cmd
        Embed r           -> k r

match :: Text -> Int -> Text -> Int -> [(Text, Text)] -> Bool
match xL nL xR nR  []                                      = xL == xR && nL == nR
match xL 0  xR 0  ((xL', xR'):_ ) | xL == xL' && xR == xR' = True
match xL nL xR nR ((xL', xR'):xs) = nL' `seq` nR' `seq` match xL nL' xR nR' xs
  where
    nL' = if xL == xL' then nL - 1 else nL
    nR' = if xR == xR' then nR - 1 else nR

instance Eq a => Eq (Expr a) where
    eL0 == eR0 = State.evalState (go (normalize eL0) (normalize eR0)) []
      where
--      go :: Expr a -> Expr a -> State [(Text, Text)] Bool
        go (Const cL) (Const cR) = return (cL == cR)
        go (Var (V xL nL)) (Var (V xR nR)) = do
            ctx <- State.get
            return (match xL nL xR nR ctx)
        go (Lam xL tL bL) (Lam xR tR bR) = do
            ctx <- State.get
            eq1 <- go tL tR
            if eq1
                then do
                    State.put ((xL, xR):ctx)
                    eq2 <- go bL bR
                    State.put ctx
                    return eq2
                else return False
        go (Pi xL tL bL) (Pi xR tR bR) = do
            ctx <- State.get
            eq1 <- go tL tR
            if eq1
                then do
                    State.put ((xL, xR):ctx)
                    eq2 <- go bL bR
                    State.put ctx
                    return eq2
                else return False
        go (App fL aL) (App fR aR) = do
            b1 <- go fL fR
            if b1 then go aL aR else return False
        go (NatLit nL) (NatLit nR) = do
            return (nL == nR)
        go Nat Nat = return True
        go NatPlus NatPlus = return True
        go NatTimes NatTimes = return True
        go (ListLit tL esL) (ListLit tR esR) = do
            b1 <- go tL tR
            if b1
                then fmap Vector.and (Vector.zipWithM go esL esR)
                else return False
        go List List = return True
        go ListAppend ListAppend = return True
        go ListEnum ListEnum = return True
        go ListFold ListFold = return True
        go ListMap  ListMap  = return True
        go (PathLit catL psL o0L) (PathLit catR psR o0R) = do
            b1 <- go catL catR
            let loop ((oL, mL):ls) ((oR, mR):rs) = do
                    b2a <- go oL oR
                    b2b <- if b2a then go mL mR else return False
                    if b2b then loop ls rs else return False
                loop [] [] = return True
                loop _  _  = return False
            b2 <- if b1 then loop psL psR else return False
            if b2 then go o0L o0R else return False
        go Path Path = return True
        go (Do mL bsL bL) (Do mR bsR bR) = do
            b1 <- go mL mR
            let loop (Bind (Arg xL _AL) rL:ls) (Bind (Arg xR _AR) rR:rs) = do
                    b2a <- go _AL _AR
                    if b2a
                        then do
                            b2b <- go rL rR
                            if b2b
                                then do
                                    ctx <- State.get
                                    State.put ((xL, xR):ctx)
                                    loop ls rs
                                else return False
                        else return False
                loop [] [] = return True
                loop _  _  = return False
            ctx <- State.get
            let Bind (Arg _ _AL) rL = bL
            let Bind (Arg _ _AR) rR = bR
            b2  <- if b1  then loop bsL bsR else return False
            b3a <- if b2  then go _AL _AR   else return False
            b3b <- if b3a then go rL rR     else return False
            State.put ctx
            return b3b
        go Cmd Cmd = return True
        go (Embed pL) (Embed pR) = return (pL == pR)
        go _ _ = return False

instance IsString (Expr a) where
    fromString str = Var (fromString str)

-- | Generates a syntactically valid Morte program
instance Buildable a => Buildable (Expr a)
  where
    build = go False False
      where
        go parenBind parenApp e = case e of
            Const c           -> build c
            Var x             -> build x
            Lam x _A b        ->
                    (if parenBind then "(" else "")
                <>  "λ("
                <>  build x
                <>  " : "
                <>  go False False _A
                <>  ") → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            Pi  x _A b        ->
                    (if parenBind then "(" else "")
                <>  (if x /= "_"
                     then "∀(" <> build x <> " : " <> go False False _A <> ")"
                     else go True False _A )
                <>  " → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            App f a           ->
                    (if parenApp then "(" else "")
                <>  go True False f <> " " <> go True True a
                <>  (if parenApp then ")" else "")
            NatLit n          -> build n
            Nat               -> "#Nat"
            NatPlus           -> "#Nat/(+)"
            NatTimes          -> "#Nat/(*)"
            ListLit t xs      ->
                    "[nil "
                <>  build t
                <>  foldMap (\x -> ", " <> build x) xs
                <>  "]"
            List              -> "#List"
            ListAppend        -> "#List/(++)"
            ListEnum          -> "#List/enum"
            ListFold          -> "#List/fold"
            ListMap           -> "#List/map"
            PathLit cat ps o0 ->
                    "[id "
                <>  build cat <> " "
                <>  mconcat (map buildStep ps)
                <>  "{ " <> build o0 <> " } "
                <>  "]"
              where
                buildStep (o, m) = "{ " <> build o <> " } " <> build m <> " "
            Path              -> "#Path"
            Do m bs b0        ->
                    "do " <> build m <> " { "
                <>  mconcat (map (\b -> build b <> " ") bs)
                <>  build b0
                <>  " }"
            Cmd               -> "#Cmd"
            Embed p           -> build p

shift :: Int -> Var -> Expr a -> Expr a
shift _ ! _      (Const k       ) = Const k
shift d !(V x n) (Var (V x' n') ) = n'' `seq` Var (V x' n'')
  where
    n'' = if x == x' && n' >= n then n' + d else n'
shift d !(V x n) (Lam x' _A b   ) = Lam x' _A' b'
  where
    _A' = shift d (V x n ) _A
    b'  = shift d (V x n') b
    n'  = if x == x' then n + 1 else n
shift d !(V x n) (Pi  x' _A _B     ) = Pi  x' _A' _B'
  where
    _A' = shift d (V x n ) _A
    _B' = shift d (V x n') _B
    n'  = if x == x' then n + 1 else n
shift d ! v      (App f a          ) = App f' a'
  where
    f' = shift d v f
    a' = shift d v a
shift _ ! _      (NatLit n         ) = NatLit n
shift _ ! _       Nat                = Nat
shift _ ! _       NatPlus            = NatPlus
shift _ ! _       NatTimes           = NatTimes
shift d ! v      (ListLit t es     ) = ListLit t' es'
  where
    t'  = shift d v t
    es' = Vector.map (shift d v) es
shift _ ! _       List               = List
shift _ ! _       ListAppend         = ListAppend
shift _ ! _       ListEnum           = ListEnum
shift _ ! _       ListFold           = ListFold
shift _ ! _       ListMap            = ListMap
shift d ! v      (PathLit cat ps o0) = PathLit cat' ps' o0'
  where
    cat' = shift d v cat
    ps'  = do
        (o, m) <- ps
        let o' = shift d v o
        let m' = shift d v m
        return (o', m')
    o0'  = shift d v o0
shift _ ! _       Path               = Path
shift d ! v0     (Do m bs0 b0      ) = Do m' bs0' b0'
  where
    m'           = shift d v0 m
    ~(v0', bs0') = go v0 bs0
      where
        go !(V x n) (Bind (Arg x' _A) r:bs) = (v', Bind (Arg x' _A') r':bs')
          where
            _A'        = shift d (V x n) _A
            r'         = shift d (V x n) r
            n'         = if x == x' then n + 1 else n
            ~(v', bs') = go (V x n') bs
        go   v       []                     = (v , []                     )
    Bind l0 r0 = b0
    Arg x0 _A0 = l0
    _A0'       = shift d v0' _A0
    l0'        = Arg x0 _A0'
    r0'        = shift d v0' r0
    b0'        = Bind l0' r0'
shift _ ! _       Cmd                = Cmd
-- The Nordom compiler enforces that all embedded values are closed expressions
shift _ ! _      (Embed p          ) = Embed p

subst :: Var -> Expr a -> Expr a -> Expr a
subst ! _      _  (Const k       ) = Const k
subst ! v      e  (Var v'        ) = if v == v' then e else Var v'
subst !(V x n) e  (Lam x' _A  b  ) = Lam x' _A' b'
  where
    n'  = if x == x' then n + 1 else n
    _A' = subst (V x n ) e  _A
    b'  = subst (V x n') e' b
      where
        e'  = shift 1 (V x' 0) e
subst !(V x n) e  (Pi  x' _A _B     ) = Pi  x' _A' _B'
  where
    n'  = if x == x' then n + 1 else n
    _A' = subst (V x n ) e  _A
    _B' = subst (V x n') e' _B
      where
        e'  = shift 1 (V x' 0) e
subst ! v      e  (App f a          ) = App f' a'
  where
    f' = subst v e f
    a' = subst v e a
subst ! _      _  (NatLit n         ) = NatLit n
subst ! _      _   Nat                = Nat
subst ! _      _   NatPlus            = NatPlus
subst ! _      _   NatTimes           = NatTimes
subst ! v      e  (ListLit t es     ) = ListLit t' es'
  where
    t'  = subst v e t
    es' = Vector.map (subst v e) es
subst ! _      _   List               = List
subst ! _      _   ListAppend         = ListAppend
subst ! _      _   ListEnum           = ListEnum
subst ! _      _   ListFold           = ListFold
subst ! _      _   ListMap            = ListMap
subst ! v      e  (PathLit cat ps o0) = PathLit cat' ps' o0'
  where
    cat' = subst v e cat
    ps'  = do
        (o, m) <- ps
        let o' = subst v e o
        let m' = subst v e m
        return (o', m')
    o0'  = subst v e o0
subst ! _      _   Path               = Path
subst ! v0     e0 (Do m bs0 b0      ) = Do m' bs0' b0'
  where
    m'                = subst v0 e0 m
    ~(v0', e0', bs0') = go v0 e0 bs0
      where
        go !(V x n) e (Bind (Arg x' _A) r:bs) = (v', e', Bind (Arg x' _A') r':bs')
          where
            _A'            = subst (V x n) e _A
            r'             = subst (V x n) e r
            n'             = if x == x' then n + 1 else n
            ~(v', e', bs') = go (V x n') (shift 1 (V x' 0) e) bs
        go   v      e  []                     = (v , e , []                      )
    Bind l0 r0 = b0
    Arg x0 _A0 = l0
    _A0'       = subst v0' e0' _A0
    l0'        = Arg x0 _A0'
    r0'        = subst v0' e0' r0
    b0'        = Bind l0' r0'
subst ! _      _   Cmd                = Cmd
-- The Nordom compiler enforces that all embedded values are closed expressions
subst ! _      _  (Embed p          ) = Embed p

-- | Reduce an expression to weak-head normal form
whnf :: Expr a -> Expr a
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (shift (-1) (V x 0) b')  -- Beta reduce
          where
            b' = subst (V x 0) a' b
              where
                a' = shift 1 (V x 0) a
        f'         -> App f' a
    _       -> e

-- | Returns whether a variable is free in an expression
freeIn :: Var -> Expr a -> Bool
freeIn ! _      (Const _          ) = False
freeIn ! v      (Var v'           ) = v == v'
freeIn !(V x n) (Lam x' _A b      ) = freeIn (V x n) _A || freeIn (V x n') b
  where
    n' = if x == x' then n + 1 else n
freeIn !(V x n) (Pi  x' _A _B     ) = freeIn (V x n) _A || freeIn (V x n') _B
  where
    n' = if x == x' then n + 1 else n
freeIn ! v      (App f a          ) = freeIn v f || freeIn v a
-- The Nordom compiler enforces that all embedded values are closed expressions
freeIn ! _      (NatLit _         ) = False
freeIn ! _       Nat                = False
freeIn ! _       NatPlus            = False
freeIn ! _       NatTimes           = False
freeIn ! v      (ListLit t es     ) = freeIn v t || any (freeIn v) es
freeIn ! _       List               = False
freeIn ! _       ListAppend         = False
freeIn ! _       ListEnum           = False
freeIn ! _       ListFold           = False
freeIn ! _       ListMap            = False
freeIn ! v      (PathLit cat ps o0) = freeIn v cat || any f ps || freeIn v o0
  where
    f (o, m) = freeIn v o || freeIn v m
freeIn ! _       Path               = False
freeIn ! v0     (Do m bs0 b       ) = freeIn v0 m || go v0 bs0
  where
    go (V x n) (Bind (Arg x' _A) r:bs) =
           freeIn (V x n) r
        || freeIn (V x n) _A
        || go (V x n') bs
      where
        n' = if x == x' then n + 1 else n
    go  v         []                    = freeIn v _A || freeIn v r
      where
        Bind (Arg _ _A) r = b
freeIn ! _       Cmd                = False
freeIn ! _      (Embed _          ) = False

-- | Normalize a Nordom expression
normalize :: Expr a -> Expr a
normalize e = case e of
    Const k           -> Const k
    Var   v           -> Var v
    Lam x _A b        -> case b' of
        App f a -> case a' of
            Var v' | v == v' && not (v `freeIn` f) ->
                shift (-1) (V x 0) f  -- Eta reduce
                   | otherwise                     ->
                e'
              where
                v = V x 0
            _                                      -> e'
          where
            a' = whnf a
        _       -> e'
      where
        b' = normalize b
        e' = Lam x (normalize _A) b'
    Pi  x _A _B       -> Pi x (normalize _A) (normalize _B)
    App f a           -> case f' of
        Lam x _A b -> normalize (shift (-1) (V x 0) b')  -- Beta reduce
          where
            b' = subst (V x 0) (shift 1 (V x 0) a') b
        _          -> case App f' a' of
            App (App NatPlus (NatLit m)) (NatLit n) ->
                NatLit (m + n)
            App (App NatTimes (NatLit m)) (NatLit n) ->
                NatLit (m * n)
            App (App (App ListAppend t) (ListLit _ xs)) (ListLit _ ys) ->
                ListLit t ((Vector.++) xs ys)
            App ListEnum (NatLit n) ->
                ListLit Nat (Vector.generate (fromIntegral n) (NatLit . fromIntegral))
            App (App (App (App ListFold _) (ListLit _ es)) p) z ->
                Vector.foldl' step z es
              where
                step x e' = normalize (App (App p x) e')
            App (App (App (App ListMap _) b) k) (ListLit _ es) ->
                ListLit b (Vector.map (\e' -> normalize (App k e')) es)
            _ -> App f' a'
      where
        f' = normalize f
        a' = normalize a
    NatLit n          -> n `seq` NatLit n
    Nat               -> Nat
    NatPlus           -> NatPlus
    NatTimes          -> NatTimes
    ListLit t es      -> ListLit (normalize t) (Vector.map normalize es)
    List              -> List
    ListAppend        -> ListAppend
    ListEnum          -> ListEnum
    ListFold          -> ListFold
    ListMap           -> ListMap
    PathLit cat ps o0 -> PathLit (normalize cat) ps' (normalize o0)
      where
        ps' = do
           (o, m) <- ps
           return (normalize o, normalize m)
    Path              -> Path
    Do m bs b0        -> Do (normalize m) bs' b0'
      where
        bs' = do
            Bind (Arg x _A) r <- bs
            return (Bind (Arg x (normalize _A)) (normalize r))
        Bind (Arg x0 _A0) r0 = b0
        b0' = Bind (Arg x0 (normalize _A0)) (normalize r0)
    Cmd               -> Cmd
    Embed p           -> Embed p

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `normalize` it afterwards.
-}
typeWith :: Context (Expr X) -> Expr X -> Either TypeError (Expr X)
typeWith ctx e = case e of
    Const c           -> fmap Const (axiom c)
    Var (V x n)       -> case Context.lookup x n ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
        Just a  -> return a
    Lam x _A b        -> do
        let ctx' = fmap (shift 1 (V x 0)) (Context.insert x _A ctx)
        _B <- typeWith ctx' b
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  x _A _B       -> do
        eS <- fmap whnf (typeWith ctx _A)
        s  <- case eS of
            Const s -> return s
            _       -> Left (TypeError ctx e (InvalidInputType _A))
        let ctx' = fmap (shift 1 (V x 0)) (Context.insert x _A ctx)
        eT <- fmap whnf (typeWith ctx' _B)
        t  <- case eT of
            Const t -> return t
            _       -> Left (TypeError ctx' e (InvalidOutputType _B))
        fmap Const (rule s t)
    App f a           -> do
        e' <- fmap whnf (typeWith ctx f)
        (x, _A, _B) <- case e' of
            Pi x _A _B -> return (x, _A, _B)
            _          -> Left (TypeError ctx e NotAFunction)
        _A' <- typeWith ctx a
        if _A == _A'
            then do
                let a'  = shift 1 (V x 0) a
                let _B' = subst (V x 0) a' _B
                return (shift (-1) (V x 0) _B')
            else do
                let nf_A  = normalize _A
                let nf_A' = normalize _A'
                Left (TypeError ctx e (TypeMismatch nf_A nf_A'))
    NatLit _          -> return Nat
    Nat               -> return (Const Star)
    NatPlus           -> return (Pi "_" Nat (Pi "_" Nat Nat))
    NatTimes          -> return (Pi "_" Nat (Pi "_" Nat Nat))
    ListLit t xs      -> do
        k <- typeWith ctx t
        if k == Const Star
            then return ()
            else Left (TypeError ctx e (InvalidListType t k))
        flip Vector.imapM_ xs (\n x -> do
            t' <- typeWith ctx x
            if t == t'
                then return ()
                else do
                    let nf_t  = normalize t
                    let nf_t' = normalize t'
                    Left (TypeError ctx e (InvalidElement n x nf_t nf_t')) )
        return (App List t)
    List              -> return (Pi "_" (Const Star) (Const Star))
    ListAppend        ->
        return
            (Pi "a" (Const Star)
                (Pi "_" (App List "a")
                    (Pi "_" (App List "a") (App List "a")) ) )
    ListEnum          -> return (Pi "_" Nat (App List Nat))
    ListFold          ->
        return
            (Pi "m" (Const Star)
                (Pi "_" (App List "m")
                    (Pi "_" (Pi "_" "m" (Pi "_" "m" "m"))
                        (Pi "_" "m" "m") ) ) )
    ListMap           ->
        return
            (Pi "a" (Const Star)
                (Pi "b" (Const Star)
                    (Pi "_" (Pi "_" "a" "b")
                        (Pi "_" (App List "a") (App List "b")) ) ) )
    PathLit cat ps o0 -> do
        k <- typeWith ctx cat
        if k == Pi "_" (Const Star) (Pi "_" (Const Star) (Const Star))
            then return ()
            else Left (TypeError ctx e (InvalidPathType cat k))
        let checkStop n o = do
                oT <- typeWith ctx o
                if oT == Const Star
                    then return ()
                    else Left (TypeError ctx e (InvalidStop n o oT))
        let checkStep n oL m oR = do
                let t = App (App cat oL) oR
                t' <- typeWith ctx m
                let nf_t  = normalize t
                let nf_t' = normalize t'
                if t == t'
                    then return ()
                    else Left (TypeError ctx e (InvalidStep n oL m oR nf_t nf_t'))
        let loop !n ((oL, m):x@(oR, _):xs) = do
                checkStop  n      oL
                -- The next check is redundant, but helps improve error messages
                checkStop (n + 1) oR
                checkStep n oL m oR
                (_, oR') <- loop (n + 1) (x:xs)
                return (oL, oR')
            loop n [(oL, m)] = do
                let oR = o0
                checkStop  n      oL
                checkStop (n + 1) oR
                checkStep n oL m oR
                return (oL, oR)
            loop n [] = do
                let oR = o0
                checkStop n oR
                return (oR, oR)
        (oL, oR) <- loop 0 ps
        return (App (App (App Path cat) oL) oR)
    Path              -> do
        let k = Pi "_" (Const Star) (Pi "_" (Const Star) (Const Star))
        return (Pi "_" k k)
    Do m bs0 b0       -> do
        k <- typeWith ctx m
        if k == Pi "_" (Const Star) (Const Star)
            then return ()
            else Left (TypeError ctx e (InvalidCmdType m k))
        let loop !n (b@(Bind a@(Arg x _A) r):bs) ctx' = do
                _AT <- typeWith ctx' _A
                if _AT == Const Star
                    then return ()
                    else Left (TypeError ctx e (InvalidReturnType n a _AT))
                let t = App m _A
                t' <- typeWith ctx' r
                if t == t'
                    then return ()
                    else Left (TypeError ctx e (InvalidAction n b t t'))
                loop (n + 1) bs (Context.insert x _A ctx')
            loop _ [] _    = return ()
        loop 0 (bs0 ++ [b0]) ctx
        return (App (App Cmd m) (argType (bindLhs b0)))
    Cmd               -> do
        let k = Pi "_" (Const Star) (Const Star)
        return (Pi "_" k k)
    Embed p           -> absurd p

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: Expr X -> Either TypeError (Expr X)
typeOf = typeWith Context.empty

-- | The specific type error
data TypeMessage
    = UnboundVariable
    | InvalidInputType (Expr X)
    | InvalidOutputType (Expr X)
    | NotAFunction
    | TypeMismatch (Expr X) (Expr X)
    | Untyped Const
    | InvalidListType (Expr X) (Expr X)
    | ListsUnsupported Const Const
    | InvalidElement Int (Expr X) (Expr X) (Expr X)
    | InvalidCmdType (Expr X) (Expr X) 
    | CmdsUnsupported Const Const
    | InvalidAction Integer (Bind X) (Expr X) (Expr X)
    | InvalidReturnType Integer (Arg X) (Expr X)
    | InvalidPathType (Expr X) (Expr X)
    | PathsUnsupported Const Const
    | InvalidStep Integer (Expr X) (Expr X) (Expr X) (Expr X) (Expr X)
    | InvalidStop Integer (Expr X) (Expr X)
    deriving (Show)

instance Buildable TypeMessage where
    build msg = case msg of
        UnboundVariable                    ->
                "Error: Unbound variable\n"
        InvalidInputType expr              ->
                "Error: Invalid input type\n"
            <>  "\n"
            <>  "Type: " <> build expr <> "\n"
        InvalidOutputType expr             ->
                "Error: Invalid output type\n"
            <>  "\n"
            <>  "Type: " <> build expr <> "\n"
        NotAFunction                       ->
                "Error: Only functions may be applied to values\n"
        TypeMismatch expr1 expr2           ->
                "Error: Function applied to argument of the wrong type\n"
            <>  "\n"
            <>  "Expected type: " <> build expr1 <> "\n"
            <>  "Actual   type: " <> build expr2 <> "\n"
        Untyped c                          ->
                "Error: " <> build c <> " has no type\n"
        InvalidListType t k                ->
                "Error: Type of the wrong kind for list elements\n"
            <>  "\n"
            <>  "Invalid type: [nil " <> build t <> " ...\n"
            <>  "                   ^\n"
            <>  "Expected kind: *\n"
            <>  "Actual   kind: " <> build k <> "\n"
        ListsUnsupported const1 const2     ->
                "Error: The current type checker rules forbid lists\n"
            <>  "\n"
            <>  "Forbidden rule: ⊦ " <> build const1 <> " ↝ " <> build const2 <> "\n"
            <>  "\n"
            <>  "Suggestion: Use an official release of Nordom.  This problem most likely means that you are using a modified version of Nordom.\n"
        InvalidElement n x t t'            ->
                "Error: List with an element of the wrong type\n"
            <>  "\n"
            <>  "Element index  : " <> build n <> "\n"
            <>  "Invalid element: " <> build x <> "\n"
            <>  "\n"
            <>  "Expected type: " <> build t  <> "\n"
            <>  "Actual   type: " <> build t' <> "\n"
        InvalidCmdType m mT                ->
                "Error: Type constructor of the wrong kind for cmd actions\n"
            <>  "\n"
            <>  "Invalid type constructor: do " <> build m <> " { ...\n"
            <>  "                             ^\n"
            <>  "Expected kind: * → *\n"
            <>  "Actual   kind: " <> build mT <> "\n"
        CmdsUnsupported const1 const2      ->
                "Error: The current type checker rules forbid cmds\n"
            <>  "\n"
            <>  "Forbidden rule: ⊦ " <> build const1 <> " ↝ " <> build const2 <> "\n"
            <>  "\n"
            <>  "Suggestion: Use an official release of Nordom.  This problem most likely means that you are using a modified version of Nordom.\n"
        InvalidAction n (Bind l r) t t'    ->
                "Error: Command with an action of the wrong type\n"
            <>  "\n"
            <>  "Action index  : " <> build n <> "\n"
            <>  prefix0 <> build r <> "\n"
            <>  prefix1 <> "^\n"
            <>  "Expected type : " <> build t <> "\n"
            <>  "Actual   type : " <> build t' <> "\n"
          where
            prefix0 = "Invalid action: " <> build l <> " <- "
            offset  = Text.length (Builder.toLazyText prefix0)
            prefix1 =
                Builder.fromLazyText (Text.replicate offset " ")
        InvalidReturnType n (Arg x _A) _AT ->
                "Error: Action with a return type of the wrong kind\n"
            <>  "\n"
            <>  "Action index  : " <> build n <> "\n"
            <>  prefix0 <> build _A <> " <- ...\n"
            <>  prefix1 <> "^\n"
            <>  "Expected kind: *\n"
            <>  "Actual   kind: " <> build _AT <> "\n"
          where
            prefix0 = "Invalid action: " <> build x <> " : "
            offset  = Text.length (Builder.toLazyText prefix0)
            prefix1 =
                Builder.fromLazyText (Text.replicate offset " ")
        InvalidPathType cat catT           ->
                "Error: Type constructor of the wrong kind for path steps\n"
            <>  "\n"
            <>  "Invalid type constructor: [id " <> build cat <> " ...\n"
            <>  "                              ^\n"
            <>  "Expected kind: * → * → *\n"
            <>  "Actual   kind: " <> build catT <> "\n"
        PathsUnsupported const1 const2     ->
                "Error: The current type checker rules forbid paths\n"
            <>  "\n"
            <>  "Forbidden rule: ⊦ " <> build const1 <> " ↝ " <> build const2 <> "\n"
            <>  "\n"
            <>  "Suggestion: Use an official release of Nordom.  This problem most likely means that you are using a modified version of Nordom.\n"
        InvalidStep n oL m oR t t' ->
                "Error: Path with a step of the wrong type\n"
            <>  "\n"
            <>  "Step index  : " <> build n <> "\n"
            <>  prefix0 <> build m <> " { " <> build oR <> " }\n"
            <>  prefix1 <> "^\n"
            <>  "Expected type: " <> build t  <> "\n"
            <>  "Actual   type: " <> build t' <> "\n"
          where
            prefix0 = "Invalid step: { " <> build oL <> " } "
            offset  = Text.length (Builder.toLazyText prefix0)
            prefix1 =
                Builder.fromLazyText (Text.replicate offset " ")
        InvalidStop n o oT         ->
                "Error: Path with a stop of the wrong kind\n"
            <>  "\n"
            <>  "Stop index  : " <> build n <> "\n"
            <>  "Invalid stop: { " <> build o <> " }\n"
            <>  "                ^\n"
            <>  "Expected kind: *\n"
            <>  "Actual   kind: " <> build oT <> "\n"

-- | A structured type error that includes context
data TypeError = TypeError
    { context     :: Context (Expr X)
    , current     :: Expr X
    , typeMessage :: TypeMessage
    } deriving (Typeable)

instance Show TypeError where
    show = Text.unpack . pretty

instance Exception TypeError

instance Buildable TypeError where
    build (TypeError ctx expr msg)
        =   "\n"
        <>  (    if Text.null (Builder.toLazyText (buildContext ctx))
                 then ""
                 else "Context:\n" <> buildContext ctx <> "\n"
            )
        <>  "Expression: " <> build expr <> "\n"
        <>  "\n"
        <>  build msg
      where
        buildKV (key, val) = build key <> " : " <> build val

        buildContext =
                build
            .   Text.unlines
            .   map (Builder.toLazyText . buildKV)
            .   reverse
            .   Context.toList

-- | Pretty-print a value
pretty :: Buildable a => a -> Text
pretty = Builder.toLazyText . build
