{-# OPTIONS_GHC -cpp -XMagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module TreeOT where

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

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

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

size :: (([]) a1) -> Prelude.Integer
size s =
  case s of
    ([]) -> 0
    (:) _ s' -> Prelude.succ (size s')

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

weak_cons ::
  Type ->
  Sort ->
  (Prelude.Maybe (([]) Sort)) ->
  Prelude.Maybe
    (([]) Sort)
weak_cons _ x =
  bind (\xs -> Prelude.Just ((:) x xs))

ins ::
  Type ->
  Prelude.Integer ->
  (([]) Sort) ->
  (([]) Sort) ->
  Prelude.Maybe
    (([]) Sort)
ins x i es xs =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Just (cat es xs))
    ( \i' ->
        case xs of
          ([]) -> Prelude.Nothing
          (:) x' xs' -> weak_cons x x' (ins x i' es xs')
    )
    i

rm ::
  Type ->
  Prelude.Integer ->
  (([]) Sort) ->
  (([]) Sort) ->
  Prelude.Maybe
    (([]) Sort)
rm x i es xs =
  case xs of
    ([]) -> case es of
      ([]) -> Prelude.Just xs
      (:) _ _ -> Prelude.Nothing
    (:) x' xs' ->
      case es of
        ([]) -> Prelude.Just xs
        (:) e' es' ->
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            ( \_ ->
                case eq_op x x' e' of
                  Prelude.True -> rm x 0 es' xs'
                  Prelude.False -> Prelude.Nothing
            )
            (\i' -> weak_cons x x' (rm x i' es xs'))
            i

nth :: Type -> Prelude.Integer -> (([]) Sort) -> Prelude.Maybe Sort
nth x index xs =
  case xs of
    ([]) -> Prelude.Nothing
    (:) x0 xs0 ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.Just x0)
        (\i -> nth x i xs0)
        index

rplc ::
  Type ->
  Prelude.Integer ->
  (Prelude.Maybe Sort) ->
  (([]) Sort) ->
  Prelude.Maybe (([]) Sort)
rplc x n e xs =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    ( \_ ->
        case xs of
          ([]) -> Prelude.Nothing
          (:) _ xs' -> bind (\e' -> Prelude.Just ((:) e' xs')) e
    )
    ( \n' ->
        case xs of
          ([]) -> Prelude.Nothing
          (:) x0 xs' -> weak_cons x x0 (rplc x n' e xs')
    )
    n

cut :: (([]) a1) -> Prelude.Integer -> Prelude.Integer -> ([]) a1
cut l sc rc =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    ( \_ ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> l)
          ( \rc' -> case l of
              ([]) -> l
              (:) _ xs -> cut xs sc rc'
          )
          rc
    )
    ( \sc' -> case l of
        ([]) -> l
        (:) x xs -> (:) x (cut xs sc' rc)
    )
    sc

data Tree t
  = Node t (([]) (Tree t))

nodeW :: a1 -> (Prelude.Maybe (([]) (Tree a1))) -> Prelude.Maybe (Tree a1)
nodeW t ls =
  case ls of
    Prelude.Just l' -> Prelude.Just (Node t l')
    Prelude.Nothing -> Prelude.Nothing

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

data OTBase x cmd
  = Build_OTBase
      (cmd -> x -> Prelude.Maybe x)
      ( cmd ->
        cmd ->
        Prelude.Bool ->
        ([]) cmd
      )

interp :: (OTBase a1 a2) -> a2 -> a1 -> Prelude.Maybe a1
interp oTBase =
  case oTBase of
    Build_OTBase interp0 _ -> interp0

it :: (OTBase a1 a2) -> a2 -> a2 -> Prelude.Bool -> ([]) a2
it oTBase =
  case oTBase of
    Build_OTBase _ it0 -> it0

transform ::
  (a1 -> a1 -> Prelude.Bool -> ([]) a1) ->
  (([]) a1) ->
  ( ([])
      a1
  ) ->
  Prelude.Integer ->
  Prelude.Maybe
    ((,) (([]) a1) (([]) a1))
transform t op1 op2 nSteps =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Nothing)
    ( \nSteps' ->
        case op1 of
          ([]) -> Prelude.Just ((,) op2 op1)
          (:) x xs ->
            case op2 of
              ([]) -> Prelude.Just ((,) op2 op1)
              (:) y ys ->
                case transform t xs (t y x Prelude.False) nSteps' of
                  Prelude.Just p ->
                    case p of
                      (,) y'' xs' ->
                        case transform t (cat (t x y Prelude.True) xs') ys nSteps' of
                          Prelude.Just p0 ->
                            case p0 of
                              (,) ys' x'' -> Prelude.Just ((,) (cat y'' ys') x'')
                          Prelude.Nothing -> Prelude.Nothing
                  Prelude.Nothing -> Prelude.Nothing
    )
    nSteps

data List_command cmd
  = TreeInsert Prelude.Integer (([]) (Tree Sort))
  | TreeRemove Prelude.Integer (([]) (Tree Sort))
  | EditLabel cmd

data Tree_command cmd
  = Atomic (List_command cmd)
  | OpenRoot Prelude.Integer (Tree_command cmd)

list_interp ::
  Type ->
  (OTBase Sort a1) ->
  (List_command a1) ->
  Sort ->
  Prelude.Maybe (Tree Sort)
list_interp x ot op1 tr =
  case unsafeCoerce tr of
    Node x0 ls ->
      case op1 of
        TreeInsert n l -> nodeW x0 (unsafeCoerce ins (tree_eqType x) n l ls)
        TreeRemove n l -> nodeW x0 (unsafeCoerce rm (tree_eqType x) n l ls)
        EditLabel c ->
          case interp ot c x0 of
            Prelude.Just x' -> Prelude.Just (Node x' ls)
            Prelude.Nothing -> Prelude.Nothing

tree_interp ::
  Type ->
  (OTBase Sort a1) ->
  (Tree_command a1) ->
  Sort ->
  Prelude.Maybe (Tree Sort)
tree_interp x ot op1 tr =
  case unsafeCoerce tr of
    Node x0 ls ->
      case op1 of
        Atomic c -> list_interp x ot c tr
        OpenRoot n c ->
          nodeW
            x0
            ( unsafeCoerce
                rplc
                (tree_eqType x)
                n
                ( bind
                    (unsafeCoerce tree_interp x ot c)
                    (nth (tree_eqType x) n (unsafeCoerce ls))
                )
                ls
            )

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

list_it ::
  Type ->
  (OTBase Sort a1) ->
  (List_command a1) ->
  ( List_command
      a1
  ) ->
  Prelude.Bool ->
  ([]) (List_command a1)
list_it x ot op1 op2 flag =
  case op1 of
    TreeInsert n1 l1 ->
      case op2 of
        TreeInsert n2 l2 ->
          case eq_op nat_eqType (unsafeCoerce n1) (unsafeCoerce n2) of
            Prelude.True ->
              case flag of
                Prelude.True -> (:) op1 ([])
                Prelude.False -> (:) (TreeInsert (addn n1 (size l2)) l1) ([])
            Prelude.False -> (:) (TreeInsert (tr_ins (size l2) n1 n2) l1) ([])
        TreeRemove n2 l2 ->
          let len = size l2
           in case leq n1 n2 of
                Prelude.True -> (:) op1 ([])
                Prelude.False ->
                  case leq (addn n2 len) n1 of
                    Prelude.True -> (:) (TreeInsert (subn n1 len) l1) ([])
                    Prelude.False -> ([])
        EditLabel _ -> (:) op1 ([])
    TreeRemove n1 l1 ->
      case op2 of
        TreeInsert n2 l2 ->
          let len1 = size l1
           in let len2 = size l2
               in case leq (addn n1 len1) n2 of
                    Prelude.True -> (:) op1 ([])
                    Prelude.False ->
                      case leq n2 n1 of
                        Prelude.True -> (:) (TreeRemove (addn n1 len2) l1) ([])
                        Prelude.False ->
                          case ins
                            (tree_eqType x)
                            (subn n2 n1)
                            (unsafeCoerce l2)
                            (unsafeCoerce l1) of
                            Prelude.Just l1' -> (:) (TreeRemove n1 (unsafeCoerce l1')) ([])
                            Prelude.Nothing -> (:) op1 ([])
        TreeRemove n2 l2 ->
          let len1 = size l1
           in let len2 = size l2
               in case leq (addn n2 len2) n1 of
                    Prelude.True -> (:) (TreeRemove (subn n1 len2) l1) ([])
                    Prelude.False ->
                      case leq (addn n1 len1) n2 of
                        Prelude.True -> (:) (TreeRemove n1 l1) ([])
                        Prelude.False ->
                          case leq n2 n1 of
                            Prelude.True ->
                              (:)
                                ( TreeRemove
                                    n2
                                    (cut l1 0 (subn (addn len2 n2) n1))
                                )
                                ([])
                            Prelude.False ->
                              (:)
                                (TreeRemove n1 (cut l1 (subn n2 n1) len2))
                                ([])
        EditLabel _ -> (:) op1 ([])
    EditLabel c1 ->
      case op2 of
        EditLabel c2 -> map (\x0 -> EditLabel x0) (it ot c1 c2 flag)
        _ -> (:) op1 ([])

tree_it ::
  Type ->
  (OTBase Sort a1) ->
  (Tree_command a1) ->
  ( Tree_command
      a1
  ) ->
  Prelude.Bool ->
  ([]) (Tree_command a1)
tree_it x ot op1 op2 flag =
  case op1 of
    Atomic c1 ->
      case c1 of
        TreeRemove n1 l1 ->
          case op2 of
            Atomic c2 -> map (\x0 -> Atomic x0) (list_it x ot c1 c2 flag)
            OpenRoot n2 tc2 ->
              case tr_rem (size l1) n2 n1 of
                Prelude.Just _ -> (:) op1 ([])
                Prelude.Nothing ->
                  let i = subn n2 n1
                   in case rplc
                        (tree_eqType x)
                        i
                        ( bind
                            (unsafeCoerce tree_interp x ot tc2)
                            (nth (tree_eqType x) i (unsafeCoerce l1))
                        )
                        (unsafeCoerce l1) of
                        Prelude.Just l1' ->
                          (:)
                            ( Atomic
                                ( TreeRemove
                                    n1
                                    (unsafeCoerce l1')
                                )
                            )
                            ([])
                        Prelude.Nothing -> (:) op1 ([])
        _ ->
          case op2 of
            Atomic c2 -> map (\x0 -> Atomic x0) (list_it x ot c1 c2 flag)
            OpenRoot _ _ -> (:) op1 ([])
    OpenRoot n1 tc1 ->
      case op2 of
        Atomic l ->
          case l of
            TreeInsert n2 l2 -> (:) (OpenRoot (tr_ins (size l2) n1 n2) tc1) ([])
            TreeRemove n2 l2 ->
              case tr_rem (size l2) n1 n2 of
                Prelude.Just n1' -> (:) (OpenRoot n1' tc1) ([])
                Prelude.Nothing -> ([])
            EditLabel _ -> (:) op1 ([])
        OpenRoot n2 tc2 ->
          case eq_op nat_eqType (unsafeCoerce n1) (unsafeCoerce n2) of
            Prelude.True ->
              map (\x0 -> OpenRoot n1 x0) (tree_it x ot tc1 tc2 flag)
            Prelude.False -> (:) op1 ([])

unitOT :: OTBase Sort ()
unitOT =
  Build_OTBase (\_ m -> Prelude.Just m) (\_ _ _ -> (:) () ([]))

it1 ::
  (([]) (Tree_command ())) ->
  (([]) (Tree_command ())) ->
  Prelude.Integer ->
  Prelude.Maybe
    ((,) (([]) (Tree_command ())) (([]) (Tree_command ())))
it1 =
  transform (tree_it nat_eqType unitOT)

abclist :: ([]) (Tree Prelude.Integer)
abclist =
  (:)
    ( Node
        ( Prelude.succ
            ( Prelude.succ
                ( Prelude.succ
                    ( Prelude.succ
                        ( Prelude.succ
                            ( Prelude.succ
                                ( Prelude.succ
                                    ( Prelude.succ
                                        ( Prelude.succ
                                            ( Prelude.succ
                                                0
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
        ([])
    )
    ( (:)
        ( Node
            ( Prelude.succ
                ( Prelude.succ
                    ( Prelude.succ
                        ( Prelude.succ
                            ( Prelude.succ
                                ( Prelude.succ
                                    ( Prelude.succ
                                        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
                                    )
                                )
                            )
                        )
                    )
                )
            )
            ([])
        )
        ( (:)
            ( Node
                ( Prelude.succ
                    ( Prelude.succ
                        ( Prelude.succ
                            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))
                        )
                    )
                )
                ([])
            )
            ([])
        )
    )

abc :: Tree Prelude.Integer
abc =
  Node (Prelude.succ 0) abclist

efg :: Tree Prelude.Integer
efg =
  Node
    (Prelude.succ (Prelude.succ 0))
    ( (:)
        ( Node
            ( Prelude.succ
                ( Prelude.succ
                    ( Prelude.succ
                        ( Prelude.succ
                            ( Prelude.succ
                                ( Prelude.succ
                                    ( Prelude.succ
                                        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))
                                    )
                                )
                            )
                        )
                    )
                )
            )
            ([])
        )
        ( (:)
            ( Node
                ( Prelude.succ
                    ( Prelude.succ
                        ( Prelude.succ
                            ( Prelude.succ
                                ( Prelude.succ
                                    ( Prelude.succ
                                        ( Prelude.succ
                                            ( Prelude.succ
                                                ( Prelude.succ
                                                    ( Prelude.succ
                                                        ( Prelude.succ
                                                            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
                ([])
            )
            ( (:)
                ( Node
                    ( Prelude.succ
                        ( Prelude.succ
                            ( Prelude.succ
                                ( Prelude.succ
                                    ( Prelude.succ
                                        ( Prelude.succ
                                            ( Prelude.succ
                                                ( Prelude.succ
                                                    ( Prelude.succ
                                                        ( Prelude.succ
                                                            ( Prelude.succ
                                                                ( Prelude.succ
                                                                    ( Prelude.succ
                                                                        ( Prelude.succ
                                                                            (Prelude.succ (Prelude.succ 0))
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                    ([])
                )
                ([])
            )
        )
    )
