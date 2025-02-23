{-# OPTIONS_GHC -cpp -XMagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module SortedTree where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified Unsafe.Coerce as GHC.Base
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

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of
    (,) x _ -> x

snd :: ((,) a1 a2) -> a2
snd p =
  case p of
    (,) _ y -> y

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of
    ([]) -> f
    (:) y l0 -> f0 y l0 (list_rect f f0 l0)

data Reflect
  = ReflectT
  | ReflectF

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

apply :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
apply f x u =
  case u of
    Prelude.Just y -> f y
    Prelude.Nothing -> x

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp _ f g x =
  f (g x)

isSome :: (Prelude.Maybe a1) -> Prelude.Bool
isSome u =
  case u of
    Prelude.Just _ -> Prelude.True
    Prelude.Nothing -> Prelude.False

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  let _evar_0_ = \_ _ _ -> ReflectT
   in let _evar_0_0 = \_ _ _ -> ReflectF
       in case pb of
            ReflectT -> _evar_0_ __ __ __
            ReflectF -> _evar_0_0 __ __ __

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

type Axiom t = t -> t -> Reflect

data Mixin_of t
  = Mixin (Rel t) (Axiom t)

op :: (Mixin_of a1) -> Rel a1
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

eqP :: Type -> Axiom Sort
eqP t =
  let _evar_0_ = \_ a -> a
   in case t of
        Mixin x x0 -> _evar_0_ x x0

inj_eqAxiom :: Type -> (a1 -> Sort) -> Axiom a1
inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

injEqMixin :: Type -> (a1 -> Sort) -> Mixin_of a1
injEqMixin eT f =
  Mixin (\x y -> eq_op eT (f x) (f y)) (inj_eqAxiom eT f)

pcanEqMixin ::
  Type ->
  (a1 -> Sort) ->
  (Sort -> Prelude.Maybe a1) ->
  Mixin_of
    a1
pcanEqMixin eT f _ =
  injEqMixin eT f

opt_eq ::
  Type ->
  (Prelude.Maybe Sort) ->
  (Prelude.Maybe Sort) ->
  Prelude.Bool
opt_eq t u v =
  apply (\x -> apply (eq_op t x) Prelude.False v) (Prelude.not (isSome v)) u

opt_eqP :: Type -> Axiom (Prelude.Maybe Sort)
opt_eqP t _top_assumption_ =
  let _evar_0_ = \x __top_assumption_ ->
        let _evar_0_ = \y -> iffP (eq_op t x y) (eqP t x y)
         in let _evar_0_0 = ReflectF
             in case __top_assumption_ of
                  Prelude.Just x0 -> _evar_0_ x0
                  Prelude.Nothing -> _evar_0_0
   in let _evar_0_0 = \__top_assumption_ ->
            let _evar_0_0 = \_ -> ReflectF
             in let _evar_0_1 = ReflectT
                 in case __top_assumption_ of
                      Prelude.Just x -> _evar_0_0 x
                      Prelude.Nothing -> _evar_0_1
       in case _top_assumption_ of
            Prelude.Just x -> _evar_0_ x
            Prelude.Nothing -> _evar_0_0

option_eqMixin :: Type -> Mixin_of (Prelude.Maybe Sort)
option_eqMixin t =
  Mixin (opt_eq t) (opt_eqP t)

option_eqType :: Type -> Type
option_eqType t =
  unsafeCoerce option_eqMixin t

ohead :: (([]) a1) -> Prelude.Maybe a1
ohead s =
  case s of
    ([]) -> Prelude.Nothing
    (:) x _ -> Prelude.Just x

head :: a1 -> (([]) a1) -> a1
head x0 s =
  case s of
    ([]) -> x0
    (:) x _ -> x

behead :: (([]) a1) -> ([]) a1
behead s =
  case s of
    ([]) -> ([])
    (:) _ s' -> s'

cat :: (([]) a1) -> (([]) a1) -> ([]) a1
cat s1 s2 =
  case s1 of
    ([]) -> s2
    (:) x s1' -> (:) x (cat s1' s2)

rcons :: (([]) a1) -> a1 -> ([]) a1
rcons s z =
  case s of
    ([]) -> (:) z ([])
    (:) x s' -> (:) x (rcons s' z)

filter :: (Pred a1) -> (([]) a1) -> ([]) a1
filter a s =
  case s of
    ([]) -> ([])
    (:) x s' ->
      case a x of
        Prelude.True -> (:) x (filter a s')
        Prelude.False -> filter a s'

eqseq :: Type -> (([]) Sort) -> (([]) Sort) -> Prelude.Bool
eqseq t s1 s2 =
  case s1 of
    ([]) -> case s2 of
      ([]) -> Prelude.True
      (:) _ _ -> Prelude.False
    (:) x1 s1' ->
      case s2 of
        ([]) -> Prelude.False
        (:) x2 s2' -> (Prelude.&&) (eq_op t x1 x2) (eqseq t s1' s2')

eqseqP :: Type -> Axiom (([]) Sort)
eqseqP t _top_assumption_ =
  let _evar_0_ = \__top_assumption_ ->
        let _evar_0_ = ReflectT
         in let _evar_0_0 = \_ _ -> ReflectF
             in case __top_assumption_ of
                  ([]) -> _evar_0_
                  (:) x x0 -> _evar_0_0 x x0
   in let _evar_0_0 = \x1 s1 iHs __top_assumption_ ->
            let _evar_0_0 = ReflectF
             in let _evar_0_1 = \x2 s2 ->
                      ssr_have
                        (eqP t x1 x2)
                        ( \__top_assumption_0 ->
                            let _evar_0_1 = \_ ->
                                  let _evar_0_1 = iffP (eqseq t s1 s2) (iHs s2)
                                   in eq_rec x1 _evar_0_1 x2
                             in let _evar_0_2 = \_ -> ReflectF
                                 in case __top_assumption_0 of
                                      ReflectT -> _evar_0_1 __
                                      ReflectF -> _evar_0_2 __
                        )
                 in case __top_assumption_ of
                      ([]) -> _evar_0_0
                      (:) x x0 -> _evar_0_1 x x0
       in list_rect _evar_0_ _evar_0_0 _top_assumption_

seq_eqMixin :: Type -> Mixin_of (([]) Sort)
seq_eqMixin t =
  Mixin (eqseq t) (eqseqP t)

seq_eqType :: Type -> Type
seq_eqType t =
  unsafeCoerce seq_eqMixin t

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f s =
  case s of
    ([]) -> ([])
    (:) x s' -> (:) (f x) (map f s')

foldr :: (a1 -> a2 -> a2) -> a2 -> (([]) a1) -> a2
foldr f z0 s =
  case s of
    ([]) -> z0
    (:) x s' -> f x (foldr f z0 s')

flatten :: (([]) (([]) a1)) -> ([]) a1
flatten =
  foldr cat ([])

bind :: (a1 -> Prelude.Maybe a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
bind f x =
  case x of
    Prelude.Just x' -> f x'
    Prelude.Nothing -> Prelude.Nothing

data Tree t
  = Node t (([]) (Tree t))

value :: (Tree a1) -> a1
value t =
  case t of
    Node v _ -> v

encode :: (Tree a1) -> ([]) (Prelude.Maybe a1)
encode t =
  case t of
    Node x f ->
      (:)
        (Prelude.Just x)
        (rcons (flatten (map encode f)) Prelude.Nothing)

decode_step ::
  (Prelude.Maybe a1) ->
  ( (,)
      (([]) (Tree a1))
      (([]) (([]) (Tree a1)))
  ) ->
  (,)
    (([]) (Tree a1))
    (([]) (([]) (Tree a1)))
decode_step c fs =
  case c of
    Prelude.Just x ->
      (,)
        ((:) (Node x (fst fs)) (head ([]) (snd fs)))
        (behead (snd fs))
    Prelude.Nothing -> (,) ([]) ((:) (fst fs) (snd fs))

decode :: (([]) (Prelude.Maybe a1)) -> Prelude.Maybe (Tree a1)
decode c =
  ohead (fst (foldr decode_step ((,) ([]) ([])) c))

tree_eqMixin :: Type -> Mixin_of (Tree Sort)
tree_eqMixin t =
  pcanEqMixin
    (seq_eqType (option_eqType t))
    (unsafeCoerce encode)
    (unsafeCoerce decode)

tree_eqType :: Type -> Type
tree_eqType t =
  unsafeCoerce tree_eqMixin t

find :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Maybe a1
find p xs =
  case xs of
    ([]) -> Prelude.Nothing
    (:) xh xt ->
      case p xh of
        Prelude.True -> Prelude.Just xh
        Prelude.False -> find p xt

type Asymmetric = ()

type Order = ()

g_insert :: Type -> (Rel Sort) -> Sort -> (([]) Sort) -> ([]) Sort
g_insert x r x0 xs =
  case xs of
    ([]) -> (:) x0 ([])
    (:) xh xt ->
      case eq_op x x0 xh of
        Prelude.True -> xs
        Prelude.False ->
          case r x0 xh of
            Prelude.True -> (:) x0 xs
            Prelude.False -> (:) xh (g_insert x r x0 xt)

type Sorted_tree =
  Tree Sort

-- singleton inductive, whose constructor was STree

sNode :: Type -> (Rel Sort) -> Sort -> Sorted_tree
sNode _ _ t =
  Node t ([])

treeR :: Type -> (Rel Sort) -> (Tree Sort) -> (Tree Sort) -> Prelude.Bool
treeR _ r x y =
  r (value x) (value y)

by_value :: Type -> Sort -> (Tree Sort) -> Prelude.Bool
by_value t v =
  funcomp () (eq_op t v) value

insert :: Type -> (Rel Sort) -> Sort -> (([]) Sort) -> ([]) Sort
insert t r =
  g_insert (tree_eqType t) (unsafeCoerce treeR t r)

without :: Type -> Sort -> (([]) (Tree Sort)) -> ([]) (Tree Sort)
without t v =
  filter (funcomp () Prelude.not (by_value t v))

type Label_preserving = ()

open ::
  Type ->
  (Rel Sort) ->
  ((Tree Sort) -> Prelude.Maybe (Tree Sort)) ->
  Sort ->
  (Tree Sort) ->
  Prelude.Maybe (Tree Sort)
open t r f vo t0 =
  case t0 of
    Node v cs ->
      case bind f (find (by_value t vo) cs) of
        Prelude.Just fch ->
          Prelude.Just
            ( Node
                v
                (unsafeCoerce insert t r fch (without t vo cs))
            )
        Prelude.Nothing -> Prelude.Nothing
