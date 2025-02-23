module OtDef where

import qualified Prelude

flip :: (a1 -> a2 -> a3) -> a2 -> a1 -> a3
flip f x y =
  f y x

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

exec_all ::
  (a1 -> a2 -> Prelude.Maybe a2) ->
  Prelude.Maybe a2 ->
  []
    a1 ->
  Prelude.Maybe a2
exec_all f =
  foldl (flip (\c -> bind (f c)))

data OTBase x cmd
  = Build_OTBase
      (cmd -> x -> Prelude.Maybe x)
      ( cmd ->
        cmd ->
        Prelude.Bool ->
        [] cmd
      )

type OTInv x cmd =
  cmd -> cmd

-- singleton inductive, whose constructor was Build_OTInv

-- OT_C2 : logical inductive
-- with constructors : Build_OT_C2
type Computability = ()

data OTComp x cmd
  = Build_OTComp (cmd -> Prelude.Integer) (cmd -> Prelude.Integer)
