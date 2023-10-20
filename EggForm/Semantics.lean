import Std.Data.HashMap
import EggForm.Syntax

namespace Semantics

open Syntax

inductive ArgumentType : Type
  | C : ArgumentType
  | N : ArgumentType
  deriving BEq

structure Signature where
  sig::
  i : List ArgumentType -- input types
  o : ArgumentType      -- output type
  deriving BEq

def Schema : Type := Std.HashMap String Signature

def constToType : Constant → ArgumentType
  | Constant.c _ => ArgumentType.C
  | Constant.n _ => ArgumentType.N

def getSignature : FunctionO Constant Constant → Signature
  | FunctionO.f (Function.f _ ins) out =>
      Signature.sig (List.map constToType ins) (constToType out)

def validSignature : Schema → FunctionO Constant Constant → Bool
  | schema, f =>
      match Std.HashMap.find? schema (functionOName f) with
      | none => false
      | some sig => sig == getSignature f