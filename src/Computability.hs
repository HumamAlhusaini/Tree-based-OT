{-# LANGUAGE LambdaCase #-}

module Computability () where

import OtDef (OTBase, OTComp (Build_OTComp), Sort, Type)
import RichText (Jcmd (JEditLabel, JInsert, JOpenRoot, JRemove, JUnite), addn)
import Tree (Tree, encode)

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

cmdsz :: OTBase a1 a2 -> OTComp a1 a2 -> a2 -> Prelude.Integer
cmdsz _ oTComp =
  case oTComp of
    Build_OTComp cmdsz0 _ -> cmdsz0

cmdsi :: OTBase a1 a2 -> OTComp a1 a2 -> a2 -> Prelude.Integer
cmdsi _ oTComp =
  case oTComp of
    Build_OTComp _ cmdsi0 -> cmdsi0

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp _ f g x =
  f (g x)

-- calculates size of computability
jsz ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  [] (Jcmd a1) ->
  Prelude.Integer
jsz x otX otcX =
  funcomp () (foldl addn 0) (map (jcmdsz x otX otcX))

-- calculates cost of computability
jsi ::
  Type ->
  OTBase Sort a1 ->
  OTComp Sort a1 ->
  [] (Jcmd a1) ->
  Prelude.Integer
jsi x otX otcX =
  funcomp () (foldl addn 0) (map (jcmdsi x otX otcX))

type Jcomputability = ()
