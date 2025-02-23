{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module RichText where

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

fst :: (,) a1 a2 -> a1
fst p =
  case p of
    (,) x _ -> x

snd :: (,) a1 a2 -> a2
snd p =
  case p of
    (,) _ y -> y

list_rect :: a2 -> (a1 -> [] a1 -> a2 -> a2) -> [] a1 -> a2
list_rect f f0 l =
  case l of
    [] -> f
    (:) y l0 -> f0 y l0 (list_rect f f0 l0)

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m = Prelude.max 0 (n Prelude.- m)

data Reflect
  = ReflectT
  | ReflectF

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

apply :: (a1 -> a2) -> a2 -> Prelude.Maybe a1 -> a2
apply f x u =
  case u of
    Prelude.Just y -> f y
    Prelude.Nothing -> x

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp _ f g x =
  f (g x)

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

eqP :: Type -> Axiom Sort
eqP t =
  let _evar_0_ _ a = a
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

eqn :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqn m n =
  (\fO fS x -> if x Prelude.== 0 then fO () else fS (x Prelude.- 1))
    ( \_ ->
        (\fO fS x -> if x Prelude.== 0 then fO () else fS (x Prelude.- 1))
          (Prelude.const Prelude.True)
          (Prelude.const Prelude.False)
          n
    )
    ( \m' ->
        (\fO fS x -> if x Prelude.== 0 then fO () else fS (x Prelude.- 1))
          (Prelude.const Prelude.False)
          (eqn m')
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

size :: [] a1 -> Prelude.Integer
size s =
  case s of
    [] -> 0
    (:) _ s' -> Prelude.succ (size s')

ohead :: [] a1 -> Prelude.Maybe a1
ohead s =
  case s of
    [] -> Prelude.Nothing
    (:) x _ -> Prelude.Just x

head :: a1 -> [] a1 -> a1
head x0 s =
  case s of
    [] -> x0
    (:) x _ -> x

behead :: [] a1 -> [] a1
behead s =
  case s of
    [] -> []
    (:) _ s' -> s'

cat :: [] a1 -> [] a1 -> [] a1
cat s1 s2 =
  case s1 of
    [] -> s2
    (:) x s1' -> (:) x (cat s1' s2)

rcons :: [] a1 -> a1 -> [] a1
rcons s z =
  case s of
    [] -> [z]
    (:) x s' -> (:) x (rcons s' z)

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

seq_eqMixin :: Type -> Mixin_of (([]) Sort)
seq_eqMixin t =
  Mixin (eqseq t) (eqseqP t)

seq_eqType :: Type -> Type
seq_eqType =
  unsafeCoerce seq_eqMixin

map :: (a1 -> a2) -> [] a1 -> [] a2
map f s =
  case s of
    [] -> []
    (:) x s' -> (:) (f x) (map f s')

foldr :: (a1 -> a2 -> a2) -> a2 -> [] a1 -> a2
foldr f z0 s =
  case s of
    [] -> z0
    (:) x s' -> f x (foldr f z0 s')

foldl :: (a2 -> a1 -> a2) -> a2 -> [] a1 -> a2
foldl f z s =
  case s of
    [] -> z
    (:) x s' -> foldl f (f z x) s'

flatten :: [] ([] a1) -> [] a1
flatten =
  foldr cat []

bind :: (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a1 -> Prelude.Maybe a2
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
weak_cons _ x =
  bind (\xs -> Prelude.Just ((:) x xs))

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

nth :: Type -> Prelude.Integer -> [] Sort -> Prelude.Maybe Sort
nth x index xs =
  case xs of
    [] -> Prelude.Nothing
    (:) x0 xs0 ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.Just x0)
        (\i -> nth x i xs0)
        index

rplc ::
  Type ->
  Prelude.Integer ->
  Prelude.Maybe Sort ->
  [] Sort ->
  Prelude.Maybe ([] Sort)
rplc x n e xs =
  (\fO fS m -> if m Prelude.== 0 then fO () else fS (m Prelude.- 1))
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

data OTBase x cmd
  = Build_OTBase
      (cmd -> x -> Prelude.Maybe x)
      ( cmd ->
        cmd ->
        Prelude.Bool ->
        [] cmd
      )

interp :: OTBase a1 a2 -> a2 -> a1 -> Prelude.Maybe a1
interp oTBase =
  case oTBase of
    Build_OTBase interp0 _ -> interp0

data OTComp x cmd
  = Build_OTComp (cmd -> Prelude.Integer) (cmd -> Prelude.Integer)

cmdsz :: OTBase a1 a2 -> OTComp a1 a2 -> a2 -> Prelude.Integer
cmdsz _ oTComp =
  case oTComp of
    Build_OTComp cmdsz0 _ -> cmdsz0

cmdsi :: OTBase a1 a2 -> OTComp a1 a2 -> a2 -> Prelude.Integer
cmdsi _ oTComp =
  case oTComp of
    Build_OTComp _ cmdsi0 -> cmdsi0

data Tree t
  = Node t ([] (Tree t))

nodeW :: a1 -> Prelude.Maybe ([] (Tree a1)) -> Prelude.Maybe (Tree a1)
nodeW t ls =
  case ls of
    Prelude.Just l' -> Prelude.Just (Node t l')
    Prelude.Nothing -> Prelude.Nothing

encode :: Tree a1 -> [] (Prelude.Maybe a1)
encode t =
  case t of
    Node x f ->
      (:)
        (Prelude.Just x)
        (rcons (flatten (map encode f)) Prelude.Nothing)

decode_step ::
  Prelude.Maybe a1 ->
  (,)
    ([] (Tree a1))
    ([] ([] (Tree a1))) ->
  (,)
    ([] (Tree a1))
    ([] ([] (Tree a1)))
decode_step c fs =
  case c of
    Prelude.Just x ->
      (,)
        ((:) (Node x (fst fs)) (head [] (snd fs)))
        (behead (snd fs))
    Prelude.Nothing -> (,) [] (Prelude.uncurry (:) fs)

decode :: [] (Prelude.Maybe a1) -> Prelude.Maybe (Tree a1)
decode c =
  ohead (fst (foldr decode_step ((,) [] []) c))

weight :: Tree a1 -> Prelude.Integer
weight t =
  Prelude.foldr
    ( addn
        Prelude.. ( \case
                      Prelude.Just _ -> Prelude.succ 0
                      Prelude.Nothing -> 0
                  )
    )
    0
    (encode t)

weights :: [] (Tree a1) -> Prelude.Integer
weights = Prelude.foldr (addn Prelude.. weight) 0

tree_eqMixin :: Type -> Mixin_of (Tree Sort)
tree_eqMixin t =
  pcanEqMixin
    (seq_eqType (option_eqType t))
    (unsafeCoerce encode)
    (unsafeCoerce decode)

tree_eqType :: Type -> Type
tree_eqType t =
  unsafeCoerce tree_eqMixin t

data Jcmd c
  = JInsert Prelude.Integer ([] (Tree Sort))
  | JRemove Prelude.Integer ([] (Tree Sort))
  | JUnite Prelude.Integer Sort ([] (Tree Sort))
  | JFlat Prelude.Integer (Tree Sort)
  | JOpenRoot Prelude.Integer (Jcmd c)
  | JEditLabel c

jinterp ::
  Type ->
  OTBase Sort a1 ->
  Jcmd a1 ->
  Tree Sort ->
  Prelude.Maybe (Tree Sort)
jinterp x otX cmd m =
  case m of
    Node x0 xs ->
      case cmd of
        JInsert i es -> nodeW x0 (unsafeCoerce ins (tree_eqType x) i es xs)
        JRemove i es -> nodeW x0 (unsafeCoerce rm (tree_eqType x) i es xs)
        JUnite i y es ->
          case es of
            [] -> Prelude.Just (Node x0 xs)
            (:) _ _ ->
              case rm (tree_eqType x) i (unsafeCoerce es) (unsafeCoerce xs) of
                Prelude.Just xs' ->
                  nodeW
                    x0
                    ( unsafeCoerce
                        ins
                        (tree_eqType x)
                        i
                        [unsafeCoerce (Node y es)]
                        xs'
                    )
                Prelude.Nothing -> Prelude.Nothing
        JFlat i t ->
          case t of
            Node z zs ->
              case nth (tree_eqType x) i (unsafeCoerce xs) of
                Prelude.Just s ->
                  case unsafeCoerce s of
                    Node y ys ->
                      case (Prelude.&&)
                        ( eq_op
                            (seq_eqType (tree_eqType x))
                            (unsafeCoerce zs)
                            (unsafeCoerce ys)
                        )
                        (eq_op x y z) of
                        Prelude.True ->
                          nodeW
                            x0
                            ( unsafeCoerce
                                oins
                                (tree_eqType x)
                                i
                                ys
                                ( rm
                                    (tree_eqType x)
                                    i
                                    [unsafeCoerce (Node y ys)]
                                    (unsafeCoerce xs)
                                )
                            )
                        Prelude.False -> Prelude.Nothing
                Prelude.Nothing -> Prelude.Nothing
        JOpenRoot i cmd' ->
          case nth (tree_eqType x) i (unsafeCoerce xs) of
            Prelude.Just x' ->
              nodeW
                x0
                ( unsafeCoerce
                    rplc
                    (tree_eqType x)
                    i
                    (unsafeCoerce jinterp x otX cmd' x')
                    xs
                )
            Prelude.Nothing -> Prelude.Nothing
        JEditLabel cmd0 ->
          case interp otX cmd0 x0 of
            Prelude.Just x' -> Prelude.Just (Node x' xs)
            Prelude.Nothing -> Prelude.Nothing

tr_ins ::
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer
tr_ins len n1 n2 =
  case leq (Prelude.succ n1) n2 of
    Prelude.True -> n1
    Prelude.False -> addn n1 len

tr_rem ::
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Maybe Prelude.Integer
tr_rem len n1 n2 =
  case leq (Prelude.succ n1) n2 of
    Prelude.True -> Prelude.Just n1
    Prelude.False ->
      case leq (addn n2 len) n1 of
        Prelude.True -> Prelude.Just (subn n1 len)
        Prelude.False -> Prelude.Nothing

tr_uni ::
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Integer ->
  Prelude.Maybe Prelude.Integer
tr_uni len n1 n2 =
  case leq (Prelude.succ n1) n2 of
    Prelude.True -> Prelude.Just n1
    Prelude.False ->
      case leq (addn n2 len) n1 of
        Prelude.True -> Prelude.Just (addn (subn n1 len) (Prelude.succ 0))
        Prelude.False -> Prelude.Nothing

openroot_in ::
  Type ->
  OTBase Sort a1 ->
  ( [] (Tree Sort) ->
    Jcmd
      a1
  ) ->
  Prelude.Integer ->
  [] (Tree Sort) ->
  Prelude.Integer ->
  Jcmd a1 ->
  [] (Jcmd a1)
openroot_in x otX cmd n1 l1 n2 tc2 =
  case tr_rem (size l1) n2 n1 of
    Prelude.Just _ -> [cmd l1]
    Prelude.Nothing ->
      let i = subn n2 n1
       in case nth (tree_eqType x) i (unsafeCoerce l1) of
            Prelude.Just x' ->
              case rplc
                (tree_eqType x)
                i
                (unsafeCoerce jinterp x otX tc2 x')
                (unsafeCoerce l1) of
                Prelude.Just l1' -> [unsafeCoerce cmd l1']
                Prelude.Nothing -> []
            Prelude.Nothing -> []

jcmdsi ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  Jcmd a1 ->
  Prelude.Integer
jcmdsi x otX otcX cmd =
  case cmd of
    JInsert _ _ -> Prelude.succ 0
    JUnite{} -> Prelude.succ 0
    JOpenRoot _ c -> jcmdsi x otX otcX c
    JEditLabel c -> cmdsi otX otcX c
    _ -> 0

jcmdsz ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  Jcmd a1 ->
  Prelude.Integer
jcmdsz x otX otcX cmd =
  case cmd of
    JInsert _ t -> weights t
    JRemove _ t -> weights t
    JOpenRoot _ c -> jcmdsz x otX otcX c
    JEditLabel c -> cmdsz otX otcX c
    _ -> Prelude.succ 0

jsz ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  [] (Jcmd a1) ->
  Prelude.Integer
jsz x otX otcX =
  funcomp () (foldl addn 0) (map (jcmdsz x otX otcX))

jsi ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  [] (Jcmd a1) ->
  Prelude.Integer
jsi x otX otcX =
  funcomp () (foldl addn 0) (map (jcmdsi x otX otcX))

type Jcomputability = ()
