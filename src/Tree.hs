module Tree (
  Tree (Node),
  idP,
  encode,
  sub,
  cat,
  tree_eqMixin,
  tree_eqType,
  interp,
  nodeW,
) where

import Eq (option_eqType, pcanEqMixin, seq_eqType, unsafeCoerce)
import OtDef (Mixin_of, OTBase (Build_OTBase), Reflect (ReflectF, ReflectT), Sort, Type)

fst :: (,) a1 a2 -> a1
fst p =
  case p of
    (,) x _ -> x

snd :: (,) a1 a2 -> a2
snd p =
  case p of
    (,) _ y -> y

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m = Prelude.max 0 (n Prelude.- m)

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of
    Prelude.True -> ReflectT
    Prelude.False -> ReflectF

rcons :: [] a1 -> a1 -> [] a1
rcons s z =
  case s of
    [] -> [z]
    (:) x s' -> (:) x (rcons s' z)

foldr :: (a1 -> a2 -> a2) -> a2 -> [] a1 -> a2
foldr f z0 s =
  case s of
    [] -> z0
    (:) x s' -> f x (Tree.foldr f z0 s')

flatten :: [] ([] a1) -> [] a1
flatten =
  Tree.foldr cat []

cat :: [] a1 -> [] a1 -> [] a1
cat s1 s2 =
  case s1 of
    [] -> s2
    (:) x s1' -> (:) x (cat s1' s2)

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

interp :: OTBase a1 a2 -> a2 -> a1 -> Prelude.Maybe a1
interp oTBase =
  case oTBase of
    Build_OTBase interp0 _ -> interp0

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
        ((:) (Node x (Tree.fst fs)) (Tree.head [] (Tree.snd fs)))
        (behead (Tree.snd fs))
    Prelude.Nothing -> (,) [] (Prelude.uncurry (:) fs)

decode :: [] (Prelude.Maybe a1) -> Prelude.Maybe (Tree a1)
decode c =
  ohead (Tree.fst (Tree.foldr decode_step ((,) [] []) c))

tree_eqMixin :: OtDef.Type -> Mixin_of (Tree Sort)
tree_eqMixin t =
  pcanEqMixin
    (seq_eqType (option_eqType t))
    (unsafeCoerce encode)
    (unsafeCoerce decode)

tree_eqType :: OtDef.Type -> OtDef.Type
tree_eqType =
  unsafeCoerce tree_eqMixin
