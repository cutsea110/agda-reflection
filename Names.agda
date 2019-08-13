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



postulate Meta : Set
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String

open import Data.Word
open import Data.Char
open import Data.Float

data Literal : Set where
  nat    : (n : ℕ)    → Literal
  word64 : (w : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}
