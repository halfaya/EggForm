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

def Schema : Type := Std.HashMap FunctionSymbol Signature

def constToType : Constant → ArgumentType
  | Constant.c _ => ArgumentType.C
  | Constant.n _ => ArgumentType.N

def getSignature : ConstantFunctionO → Signature
  |  ((_, ins), out) =>
      Signature.sig (List.map constToType ins) (constToType out)

def validSignature : Schema → ConstantFunctionO → Bool
  | schema, f@((fname,_),_) =>
      match Std.HashMap.find? schema fname with
      | none => false
      | some sig => sig == getSignature f

def boolToType : Bool → Type
  | false => Empty
  | true => Unit

structure Database where
  db::
  schema: Schema
  functions: List ((f : ConstantFunctionO) × (boolToType (validSignature schema f)))

-- Note that there could be multiple functions with the same input
-- and different outputs in the DB. This just finds the first one.
def dblookup : ConstantFunction → Database → Option Constant
  | f, (Database.db _ xs) => List.lookup f (List.map Sigma.fst xs)

def defaultOutput : ConstantFunctionO → Constant
| (_, Constant.c _) => ⊥
| (_, Constant.n _) => Constant.n 0 -- TODO: Create fresh constant

/-
def flattenAux1 : GroundAtom → Constant × List (FunctionO Term Constant)
  | GroundAtom.t (Term.c c) => (c, [])
  | GroundAtom.t (Term.f (Function.f f args)) =>
      let xs := List.map (flattenAux ∘ GroundAtom.t) args; (⊥, [])
  | GroundAtom.b (FunctionO.f (Function.f f args) c) =>
      let xs := List.map (flattenAux ∘ GroundAtom.t) args
      let cs : List Term := List.map (Term.c ∘ Prod.fst) xs
      let fs : List (List (FunctionO Term Constant)) := List.map Prod.snd xs
      (c , [FunctionO.f (Function.f f cs) c])
      -/

-- TODO: prove termination
-- TODO: add support for fresh uninterpreted constants
unsafe def flattenAux : Dababase → Term → Constant × List ConstantFunctionO
  | _, Term.c c => (c, [])
  | db, Term.f f args =>
      let xs : List (Constant × List ConstantFunctionO) := List.map (flattenAux db) args
      let cs := List.map (·.1) xs
      let fs := List.map (·.2) xs
      let (v : Constant) := match dblookup (f, cs) db with
        | Option.some x => x
        | Option.none => defaultOutput (f, cs)
      (v, [((f,cs),v)])
