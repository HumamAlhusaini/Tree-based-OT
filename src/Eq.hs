module Eq (pcanEqMixin, seq_eqType, iffP, eq_op, unsafeCoerce, option_eqType) where

import OtDef (Axiom, Mixin_of (Mixin), Reflect (ReflectF, ReflectT), Rel, Sort, Type)
import qualified Unsafe.Coerce as GHC.Base

unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce

__ :: any
__ = Prelude.error "Logical or arity value used"

list_rect :: a2 -> (a1 -> [] a1 -> a2 -> a2) -> [] a1 -> a2
list_rect f f0 l =
  case l of
    [] -> f
    (:) y l0 -> f0 y l0 (list_rect f f0 l0)

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

isSome :: Prelude.Maybe a1 -> Prelude.Bool
isSome u =
  case u of
    Prelude.Just _ -> Prelude.True
    Prelude.Nothing -> Prelude.False

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  let _evar_0_ _ _ _ = ReflectT
   in let _evar_0_0 _ _ _ = ReflectF
       in case pb of
            ReflectT -> _evar_0_ __ __ __
            ReflectF -> _evar_0_0 __ __ __

apply :: (a1 -> a2) -> a2 -> Prelude.Maybe a1 -> a2
apply f x u =
  case u of
    Prelude.Just y -> f y
    Prelude.Nothing -> x

class0 :: Type -> Mixin_of Sort
class0 cT =
  cT

op :: Mixin_of a1 -> Rel a1
op m =
  case m of
    Mixin op0 _ -> op0

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

eqP :: Type -> Axiom Sort
eqP t =
  let _evar_0_ _ a = a
   in case t of
        Mixin x x0 -> _evar_0_ x x0

opt_eq ::
  Type ->
  Prelude.Maybe Sort ->
  Prelude.Maybe Sort ->
  Prelude.Bool
opt_eq t u v =
  apply (\x -> apply (eq_op t x) Prelude.False v) (Prelude.not (isSome v)) u

opt_eqP :: Type -> Axiom (Prelude.Maybe Sort)
opt_eqP t _top_assumption_ =
  let _evar_0_ x __top_assumption_ =
        let _evar_0_ y = iffP (eq_op t x y) (eqP t x y)
         in let _evar_0_0 = ReflectF
             in case __top_assumption_ of
                  Prelude.Just x0 -> _evar_0_ x0
                  Prelude.Nothing -> _evar_0_0
   in let _evar_0_0 __top_assumption_ =
            let _evar_0_0 = Prelude.const ReflectF
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
option_eqType =
  unsafeCoerce option_eqMixin

seq_eqMixin :: Type -> Mixin_of ([] Sort)
seq_eqMixin t =
  Mixin (eqseq t) (eqseqP t)

seq_eqType :: Type -> Type
seq_eqType =
  unsafeCoerce seq_eqMixin

inj_eqAxiom :: OtDef.Type -> (a1 -> Sort) -> Axiom a1
inj_eqAxiom eT f x y =
  iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

injEqMixin :: OtDef.Type -> (a1 -> Sort) -> Mixin_of a1
injEqMixin eT f =
  Mixin (\x y -> eq_op eT (f x) (f y)) (inj_eqAxiom eT f)
pcanEqMixin ::
  OtDef.Type ->
  (a1 -> Sort) ->
  (Sort -> Prelude.Maybe a1) ->
  Mixin_of
    a1
pcanEqMixin eT f _ =
  injEqMixin eT f

eqseq :: Type -> [] Sort -> [] Sort -> Prelude.Bool
eqseq t s1 s2 =
  case s1 of
    [] -> case s2 of
      [] -> Prelude.True
      (:) _ _ -> Prelude.False
    (:) x1 s1' ->
      case s2 of
        [] -> Prelude.False
        (:) x2 s2' -> (Prelude.&&) (eq_op t x1 x2) (eqseq t s1' s2')

eqseqP :: Type -> Axiom ([] Sort)
eqseqP t _top_assumption_ =
  let _evar_0_ __top_assumption_ =
        let _evar_0_ = ReflectT
         in let _evar_0_0 _ _ = ReflectF
             in case __top_assumption_ of
                  [] -> _evar_0_
                  (:) x x0 -> _evar_0_0 x x0
   in let _evar_0_0 x1 s1 iHs __top_assumption_ =
            let _evar_0_0 = ReflectF
             in let _evar_0_1 x2 s2 =
                      ssr_have
                        (eqP t x1 x2)
                        ( \__top_assumption_0 ->
                            let _evar_0_1 _ =
                                  let _evar_0_1 = iffP (eqseq t s1 s2) (iHs s2)
                                   in eq_rec x1 _evar_0_1 x2
                             in let _evar_0_2 _ = ReflectF
                                 in case __top_assumption_0 of
                                      ReflectT -> _evar_0_1 __
                                      ReflectF -> _evar_0_2 __
                        )
                 in case __top_assumption_ of
                      [] -> _evar_0_0
                      (:) x x0 -> _evar_0_1 x x0
       in list_rect _evar_0_ _evar_0_0 _top_assumption_
