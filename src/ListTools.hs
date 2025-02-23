{-# OPTIONS_GHC -cpp -XMagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module ListTools where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Exts as GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce# 
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

type Sig a = a

-- singleton inductive, whose constructor was exist

data Reflect
  = ReflectT
  | ReflectF

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

newtype Mem_pred t
  = Mem (Pred t)

data PredType0 t
  = PredType (Any -> Pred t) (Any -> Mem_pred t)

type Pred_sort t = Any

mkPredType :: (a2 -> a1 -> Prelude.Bool) -> PredType0 a1
mkPredType toP =
  PredType (unsafeCoerce toP) (\p -> Mem (\x -> unsafeCoerce toP p x))

pred_of_mem :: (Mem_pred a1) -> Pred_sort a1
pred_of_mem mp =
  case mp of
    Mem p -> unsafeCoerce p

mem :: (PredType0 a1) -> (Pred_sort a1) -> Mem_pred a1
mem pT =
  case pT of
    PredType _ s -> s

in_mem :: a1 -> (Mem_pred a1) -> Prelude.Bool
in_mem x mp =
  unsafeCoerce pred_of_mem mp x

predType :: (a2 -> Pred a1) -> PredType0 a1
predType =
  mkPredType

type Axiom t = t -> t -> Reflect

data Mixin_of t
  = Mixin (Rel t) (Axiom t)

op :: Mixin_of a1 -> Rel a1
op m =
  case m of
    Mixin op0 _ -> op0

type Type = Mixin_of Any

-- singleton inductive, whose constructor was Pack

type Sort = Any

class0 :: Type -> Mixin_of Sort
class0 cT =
  cT

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

cat :: (([]) a1) -> (([]) a1) -> ([]) a1
cat s1 s2 =
  case s1 of
    ([]) -> s2
    (:) x s1' -> (:) x (cat s1' s2)

filter :: (Pred a1) -> (([]) a1) -> ([]) a1
filter a s =
  case s of
    ([]) -> ([])
    (:) x s' ->
      case a x of
        Prelude.True -> (:) x (filter a s')
        Prelude.False -> filter a s'

mem_seq :: Type -> [] Sort -> Sort -> Prelude.Bool
mem_seq t s =
  case s of
    [] -> (\_ -> Prelude.False)
    (:) y s' ->
      let p = mem_seq t s' in (\x -> (Prelude.||) (eq_op t x y) (p x))

type Seq_eqclass = [] Sort

pred_of_seq :: Type -> Seq_eqclass -> Pred_sort Sort
pred_of_seq t s =
  unsafeCoerce mem_seq t s

seq_predType :: Type -> PredType0 Sort
seq_predType t =
  predType (unsafeCoerce pred_of_seq t)

bind :: (a1 -> Prelude.Maybe a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
bind f x =
  case x of
    Prelude.Just x' -> f x'
    Prelude.Nothing -> Prelude.Nothing

weak_cons ::
  Type ->
  Sort ->
  Prelude.Maybe ([] Sort) ->
  Prelude.Maybe
    ([] Sort)
-- this implements currying
weak_cons _ x =
  bind (\xs -> Prelude.Just ((:) x xs))

weak_app ::
  Type ->
  [] Sort ->
  Prelude.Maybe ([] Sort) ->
  Prelude.Maybe ([] Sort)
weak_app _ xs ys =
  case ys of
    Prelude.Just ys0 -> Prelude.Just (cat xs ys0)
    Prelude.Nothing -> Prelude.Nothing

ins ::
  Type ->
  Prelude.Integer ->
  [] Sort ->
  [] Sort ->
  Prelude.Maybe
    ([] Sort)
ins x i es xs =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Just (cat es xs))
    ( \i' ->
        case xs of
          [] -> Prelude.Nothing
          (:) x' xs' -> weak_cons x x' (ins x i' es xs')
    )
    i

oins ::
  Type ->
  Prelude.Integer ->
  [] Sort ->
  Prelude.Maybe ([] Sort) ->
  Prelude.Maybe ([] Sort)
oins x i es =
  bind (ins x i es)

rm ::
  Type ->
  Prelude.Integer ->
  [] Sort ->
  [] Sort ->
  Prelude.Maybe
    ([] Sort)
rm x i es xs =
  case xs of
    [] -> case es of
      [] -> Prelude.Just xs
      (:) _ _ -> Prelude.Nothing
    (:) x' xs' ->
      case es of
        [] -> Prelude.Just xs
        (:) e' es' ->
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            ( \_ ->
                case eq_op x x' e' of
                  Prelude.True -> rm x 0 es' xs'
                  Prelude.False -> Prelude.Nothing
            )
            (\i' -> weak_cons x x' (rm x i' es xs'))
            i

orm ::
  Type ->
  Prelude.Integer ->
  [] Sort ->
  Prelude.Maybe ([] Sort) ->
  Prelude.Maybe ([] Sort)
orm x index elements =
  bind (rm x index elements)

rplc ::
  Type ->
  Prelude.Integer ->
  Prelude.Maybe Sort ->
  [] Sort ->
  Prelude.Maybe ([] Sort)
rplc x n e xs =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    ( \_ ->
        case xs of
          [] -> Prelude.Nothing
          (:) _ xs' -> bind (\e' -> Prelude.Just ((:) e' xs')) e
    )
    ( \n' ->
        case xs of
          [] -> Prelude.Nothing
          (:) x0 xs' -> weak_cons x x0 (rplc x n' e xs')
    )
    n

orplc ::
  Type ->
  Prelude.Integer ->
  Prelude.Maybe Sort ->
  Prelude.Maybe
    ([] Sort) ->
  Prelude.Maybe ([] Sort)
orplc x index e =
  bind (rplc x index e)

seqminus :: Type -> [] Sort -> [] Sort -> [] Sort
seqminus x x0 y =
  filter
    ( \z ->
        Prelude.not (in_mem z (mem (seq_predType x) (unsafeCoerce y)))
    )
    x0
