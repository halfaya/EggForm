import Std.Data.HashMap
import EggForm.Syntax

namespace Semantics

open Syntax

inductive FunctionType : Type
  | N : FunctionType
  | C : FunctionType

structure Signature where
  sig::
  i : List FunctionType -- input types
  o : FunctionType      -- output type

def Schema : Type := Std.HashMap String Int
