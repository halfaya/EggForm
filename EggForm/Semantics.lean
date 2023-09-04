import Std.Data.HashMap
import EggForm.Syntax

namespace Semantics

open Syntax

inductive FunctionType : Type
  | C : FunctionType
  | N : FunctionType
  deriving BEq

structure Signature where
  sig::
  i : List FunctionType -- input types
  o : FunctionType      -- output type
  deriving BEq

def Schema : Type := Std.HashMap String Signature

def constToType : Constant → FunctionType
  | Constant.c _ => FunctionType.C
  | Constant.n _ => FunctionType.N

def getSignature : FunctionO Constant Constant → Signature
  | FunctionO.f (Function.f _ ins) out =>
      Signature.sig (List.map constToType ins) (constToType out)

def validSignature : Schema → FunctionO Constant Constant → Bool
  | schema, f =>
      match Std.HashMap.find? schema (functionOName f) with
      | none => false
      | some sig => sig == getSignature f
