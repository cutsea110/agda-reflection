module Names where

open import Data.Bool
open import Data.Nat
open import Data.String

postulate
  Name : Set
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

nameOfℕ : Name
nameOfℕ = quote ℕ

nameOfBool : Name
nameOfBool = quote Bool

isℕ : Name → Bool
isℕ (quote ℕ) = true
isℕ _         = false

isBool : Name → Bool
isBool (quote Bool) = true
isBool _            = false
