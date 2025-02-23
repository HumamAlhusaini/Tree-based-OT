{-# OPTIONS_GHC -cpp -XMagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module ArithAux where

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

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

data Reflect
  = ReflectT
  | ReflectF

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  let _evar_0_ = \_ _ _ -> ReflectT
   in let _evar_0_0 = \_ _ _ -> ReflectF
       in case pb of
            ReflectT -> _evar_0_ __ __ __
            ReflectF -> _evar_0_0 __ __ __

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of
    Prelude.True -> ReflectT
    Prelude.False -> ReflectF

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

eqn :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqn m n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    ( \_ ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> Prelude.True)
          (\_ -> Prelude.False)
          n
    )
    ( \m' ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> Prelude.False)
          (\n' -> eqn m' n')
          n
    )
    m

eqnP :: Axiom Prelude.Integer
eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

nat_eqMixin :: Mixin_of Prelude.Integer
nat_eqMixin =
  Mixin eqn eqnP

nat_eqType :: Type
nat_eqType =
  unsafeCoerce nat_eqMixin

addn_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn_rec =
  (Prelude.+)

addn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
addn =
  addn_rec

subn_rec :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
subn_rec =
  sub

subn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
subn =
  subn_rec

leq :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leq m n =
  eq_op nat_eqType (unsafeCoerce subn m n) (unsafeCoerce 0)

-- interval_point : logical inductive
-- with constructors : IP_Left IP_Right IP_Inside
-- interval_point_inclusive : logical inductive
-- with constructors : IPI_Left IPI_Right IPI_Inside
data Ii_choice z
  = MkIIChoice z z z z z z z

ii_f12 :: (Ii_choice a1) -> a1
ii_f12 i =
  case i of
    MkIIChoice ii_f13 _ _ _ _ _ _ -> ii_f13

ii_f21 :: (Ii_choice a1) -> a1
ii_f21 i =
  case i of
    MkIIChoice _ ii_f22 _ _ _ _ _ -> ii_f22

ii_feq :: (Ii_choice a1) -> a1
ii_feq i =
  case i of
    MkIIChoice _ _ ii_feq0 _ _ _ _ -> ii_feq0

ii_f121 :: (Ii_choice a1) -> a1
ii_f121 i =
  case i of
    MkIIChoice _ _ _ ii_f122 _ _ _ -> ii_f122

ii_f212 :: (Ii_choice a1) -> a1
ii_f212 i =
  case i of
    MkIIChoice _ _ _ _ ii_f213 _ _ -> ii_f213

ii_f2121 :: (Ii_choice a1) -> a1
ii_f2121 i =
  case i of
    MkIIChoice _ _ _ _ _ ii_f2122 _ -> ii_f2122

ii_f1212 :: (Ii_choice a1) -> a1
ii_f1212 i =
  case i of
    MkIIChoice _ _ _ _ _ _ ii_f1213 -> ii_f1213

interval_interval_case ::
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer ->
  ( Ii_choice
      a1
  ) ->
  a1
interval_interval_case n1 len1 n2 len2 c =
  case (Prelude.&&)
    (eq_op nat_eqType (unsafeCoerce n1) (unsafeCoerce n2))
    (eq_op nat_eqType (unsafeCoerce len1) (unsafeCoerce len2)) of
    Prelude.True -> ii_feq c
    Prelude.False ->
      case leq (addn n1 len1) n2 of
        Prelude.True -> ii_f12 c
        Prelude.False ->
          case leq (addn n2 len2) n1 of
            Prelude.True -> ii_f21 c
            Prelude.False ->
              case leq n2 n1 of
                Prelude.True ->
                  case leq (addn n1 len1) (addn n2 len2) of
                    Prelude.True -> ii_f212 c
                    Prelude.False ->
                      case eq_op nat_eqType (unsafeCoerce n1) (unsafeCoerce n2) of
                        Prelude.True -> ii_f121 c
                        Prelude.False -> ii_f2121 c
                Prelude.False ->
                  case leq (addn n2 len2) (addn n1 len1) of
                    Prelude.True -> ii_f121 c
                    Prelude.False -> ii_f1212 c

-- interval_cases_analysis : logical inductive
-- with constructors : I_12 I_21 I_eq I_121 I_212 I_1212 I_2121
-- interval_interval_case_anal : logical inductive
-- with constructors : II_12 II_21 II_eq II_121 II_212 II_1212 II_2121
