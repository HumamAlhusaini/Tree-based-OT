module Commons where

import qualified Prelude

bind :: (a1 -> Prelude.Maybe a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
bind f x =
  case x of {
   Prelude.Just x' -> f x';
   Prelude.Nothing -> Prelude.Nothing}

fmap :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
fmap f ox =
  case ox of {
   Prelude.Just x -> Prelude.Just (f x);
   Prelude.Nothing -> Prelude.Nothing}

type Maybe = ()

