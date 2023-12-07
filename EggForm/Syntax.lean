namespace Syntax

def C : Type := Nat -- interpreted constant
  deriving BEq

def N : Type := Nat -- uninterpreted constant
  deriving BEq

instance : Add N where
  add := Nat.add

instance : OfNat N n where
  ofNat := n

def nextN (n: N) : N := n + 1

def Variable : Type := Nat
abbrev FunctionSymbol : Type := String

inductive Constant : Type
  | c : C → Constant
  | n : N → Constant
  deriving BEq

notation "⊥" => Constant.c (0 : Nat)

abbrev ConstantFunction : Type := FunctionSymbol × List Constant
abbrev ConstantFunctionO : Type := ConstantFunction × Constant -- constant function with constant output

inductive BasePattern : Type
  | c : Constant → BasePattern
  | v : Variable → BasePattern

inductive Term : Type -- also called ground term
  | c : Constant → Term
  | f : FunctionSymbol → List Term → Term
  deriving BEq

inductive Pattern : Type
  | b : BasePattern → Pattern
  | f : FunctionSymbol → List Pattern → Pattern

inductive Atom : Type
  | f : FunctionSymbol → List Pattern → Atom
  | b : FunctionSymbol → List Pattern → BasePattern → Atom

inductive GroundAtom : Type
  | t : Term → GroundAtom
  | b : FunctionSymbol → List Term → Constant → GroundAtom

inductive Rule : Type
  | rule : Atom → List Atom → Rule

inductive Program : Type
  | program : List Rule → Program
