namespace Syntax

def C : Type := Nat -- interpreted constant
def N : Type := Nat -- uninterpreted constant
def Variable : Type := Nat
abbrev FunctionSymbol : Type := String

inductive Constant : Type
  | c : C → Constant
  | n : N → Constant

inductive BasePattern : Type
  | c : Constant → BasePattern
  | v : Variable → BasePattern

inductive Function (T : Type) : Type
  | f : FunctionSymbol → List T → Function T

def functionName : {T : Type} → Function T → FunctionSymbol
  | _, (Function.f name _) => name

-- function with output
inductive FunctionO (T : Type) (O : Type) : Type
  | f : Function T → O → FunctionO T O

def functionOName : {T O : Type} → FunctionO T O → FunctionSymbol
  | _, _, (FunctionO.f f _) => functionName f

inductive Term : Type -- also called ground term
  | c : Constant → Term
  | f : Function Term → Term

inductive Pattern : Type
  | b : BasePattern → Pattern
  | f : Function Pattern → Pattern

inductive Atom : Type
  | f : Function Pattern → Atom
  | b : FunctionO Pattern BasePattern → Atom

inductive GroundAtom : Type
  | f : Function Term → GroundAtom
  | b : FunctionO Term Constant → GroundAtom

inductive Rule : Type
  | rule : Atom → List Atom → Rule

inductive Program : Type
  | program : List Rule → Program

