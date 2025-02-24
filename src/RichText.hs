{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module RichText (Jcmd (JInsert, JRemove, JOpenRoot, JEditLabel, JUnite), unsafeCoerce, addn) where

import Eq (eq_op, iffP, seq_eqType)
import OtDef (Axiom, Mixin_of (Mixin), OTBase, Sort, Type)
import Tree (Tree (Node), cat, idP, interp, nodeW, sub, tree_eqType)
import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified Unsafe.Coerce as GHC.Base
#else
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

-- singleton inductive, whose constructor was Pack

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

rcons :: [] a1 -> a1 -> [] a1
rcons s z =
  case s of
    [] -> [z]
    (:) x s' -> (:) x (rcons s' z)

map :: (a1 -> a2) -> [] a1 -> [] a2
map f s =
  case s of
    [] -> []
    (:) x s' -> (:) (f x) (map f s')

foldl :: (a2 -> a1 -> a2) -> a2 -> [] a1 -> a2
foldl f z s =
  case s of
    [] -> z
    (:) x s' -> foldl f (f z x) s'

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

data Jcmd c
  = JInsert Prelude.Integer ([] (Tree Sort)) -- Inserts subtrees es at position i in xs.
  | JRemove Prelude.Integer ([] (Tree Sort)) -- Removes subtrees es at position i in xs.
  | JUnite Prelude.Integer Sort ([] (Tree Sort)) -- Unite node at index with subtrees
  | JFlat Prelude.Integer (Tree Sort) -- Flatten tree at index
  | JOpenRoot Prelude.Integer (Jcmd c) -- Apply command to root of subtree at index
  | JEditLabel c -- Modify label of root node

jinterp ::
  Type ->
  OTBase Sort a1 -> -- A base OT function for editing Sort labels.
  Jcmd a1 -> -- The command to apply.
  Tree Sort -> -- The tree being modified.
  Prelude.Maybe (Tree Sort) -- If modification succeeds, returns Prelude.Just, else prelude.Nothing
jinterp x otX cmd m =
  case m of
    Node x0 xs ->
      -- Matches the root node Node x0 xs, where: x0: Label of the root. xs: List of child subtrees.
      case cmd of
        JInsert i es -> nodeW x0 (unsafeCoerce ins (tree_eqType x) i es xs) -- Inserts subtrees es at position i in xs.
        JRemove i es -> nodeW x0 (unsafeCoerce rm (tree_eqType x) i es xs) -- Removes subtrees es at position i in xs.
        JUnite i y es ->
          {-
              If es is empty, returns the tree unchanged.
              Otherwise:
                Removes es from index i (rm).
                Inserts a new node (Node y es) at index i (ins).
          -}
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
          {-
            Flattens a tree node at index i, but only if:

            The subtrees zs match the subtrees ys.
            The labels x, y, z are equal (eq_op x y z).

            If both conditions hold, it removes the node and inserts its children at index i.
          -}
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
          -- Finds the subtree at index i and applies cmd' to its root.
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
          {-
              Modifies the root node’s label (x0) using interp otX cmd0 x0.
              If successful, updates x0 in the tree.
          -}
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
