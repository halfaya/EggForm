{-# OPTIONS --without-K --safe #-}

module Syntax where

open import Prelude

IConst UConst Variable : Type
IConst   = ℕ
UConst   = ℕ
Variable = ℕ

data Const : Type where
  icon : IConst → Const
  ucon : UConst → Const

data BasePattern : Type where
  conpat : Const → BasePattern
  varpat : Variable → BasePattern

FunSymbol : Type
FunSymbol = String

data Function (T : Type) : Type where
  f : FunSymbol → List T → Function T

data Term : Type where
  conterm : Const → Term
  funterm : Function Term → Term

data Pattern : Type where
  basepat : BasePattern → Pattern
  funpat  : Function Pattern → Pattern

data Atom : Type where
  funpat  : Function Pattern → Atom
  bfunpat : Function Pattern → BasePattern → Atom

data Rule : Type where
  rule : Atom → List Atom → Rule

data Program : Type where
  program : List Rule → Program


