module Day02 where

open import IO
open import Function
open import Data.Bool hiding (_≟_)
open import Data.Char using (_≟_; Char)

open import Data.Nat hiding (_≟_)
open import Data.Nat.ListAction using (sum)
open import Data.Bool.ListAction using (any)
open import Data.Nat.Properties using (m^n≢0)

open import Data.List hiding ([_]; sum; any)
open import Data.List.Relation.Binary.Infix.Heterogeneous.Properties using (infix?)
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.String using (String)

open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_])
open import Relation.Nullary.Decidable using (does)

import Data.Nat.Show as NatShow
import Data.List as List
import Data.String as String
import Data.Nat.Properties as NatProperties
import Data.List.Extrema NatProperties.≤-totalOrder as Extrema

record Range : Set where
  field
    min : ℕ
    max : ℕ
    digits : ℕ
    evenDigits : digits ≥ 2 × digits % 2 ≡ 0

parseRange : String → Maybe (ℕ × ℕ)
parseRange rng with String.wordsBy (_≟ '-') rng
... | left ∷ right ∷ [] with NatShow.readMaybe 10 left | NatShow.readMaybe 10 right
... | just l | just r = just (l , r)
... | _ | _ = nothing
parseRange rng | _ = nothing

clean : String → String
clean s with (unsnoc (String.toList s))
... | just (xs , _) = String.fromList xs
... | nothing = ""

parse : String → List (ℕ × ℕ)
parse = List.catMaybes ∘ List.map parseRange ∘ String.wordsBy (_≟ ',') ∘ clean

numDigits : ℕ → ℕ
numDigits n = String.length (NatShow.show n)

minOfDigits : ℕ → ℕ
minOfDigits 0 = 1
minOfDigits 1 = 1
minOfDigits (suc n) = 10 ^ n

maxOfDigits : ℕ → ℕ
maxOfDigits 0 = 0
maxOfDigits n = (minOfDigits (suc n)) ∸ 1

{-# TERMINATING #-}
expand : List (ℕ × ℕ) → List (ℕ × ℕ)
expand xs = concat (List.map expandOne xs)
  where
    expandOne : (ℕ × ℕ) → List (ℕ × ℕ)
    expandOne (min , max) =
      let minDigits = numDigits min
          highDigits = maxOfDigits minDigits
      in if minDigits ≡ᵇ (numDigits max) then (min , max) ∷ [] else (min , maxOfDigits minDigits) ∷ expandOne (suc highDigits , max)

keepValidRanges : List (ℕ × ℕ) → List Range
keepValidRanges = List.catMaybes ∘ List.map parseAsRange
  where
    constructRange : (ℕ × ℕ) × ℕ → Maybe (Range)
    constructRange ((min , max) , zero) = nothing
    constructRange ((min , max) , suc zero) = nothing
    constructRange ((min , max) , suc (suc n)) with (suc (suc n)) % 2 | inspect (_% 2) (suc (suc n))
    ... | zero | [ eq ] = just (record { min = min ; max = max ; digits = suc (suc n) ; evenDigits = s≤s (s≤s z≤n) , eq })
    ... | _ | _ = nothing

    parseAsRange : ℕ × ℕ → Maybe (Range)
    parseAsRange range = constructRange (range , numDigits (proj₁ range))

⌈_/_⌉ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
⌈ m / n ⌉ = let div = m / n
                mul = div * n
            in if mul ≡ᵇ m then div else suc div

lowRange : Range → ℕ
lowRange r = let d = (Range.digits r) / 2
                 low₁ = 10 ^ (d ∸ 1)
                 low₂ = ⌈ (Range.min r) / suc (10 ^ d) ⌉
             in low₂

highRange : Range → ℕ
highRange r = let d = (Range.digits r) / 2
                  high₁ = (10 ^ d) ∸ 1
                  high₂ = (Range.max r) / suc (10 ^ d)
              in high₂

sumFromTo : ℕ → ℕ → ℕ
sumFromTo min max = if min ≤ᵇ max then ((suc (max ∸ min)) * (min + max)) / 2 else 0

sumInvalidIdsInRange : Range → ℕ
sumInvalidIdsInRange r = (suc (10 ^ ((Range.digits r) / 2))) * (sumFromTo (lowRange r) (highRange r))

part1 : List (ℕ × ℕ) → ℕ
part1 = sum ∘ List.map sumInvalidIdsInRange ∘ keepValidRanges ∘ expand

range : (ℕ × ℕ) → List ℕ
range (min , max) with max ∸ min
... | diff = List.map (min +_) (upTo (suc diff))

generate : (maxDigits : ℕ) .{{_ : NonZero maxDigits}} → List (ℕ × ℕ)
generate maxDigits = List.concatMap generateReps $ range (1 , maxDigits / 2)
  where
    generateReps : ℕ → List (ℕ × ℕ)
    generateReps zero = []
    generateReps (suc n) = List.map (suc n ,_ ) $ range (2 , maxDigits / (suc n))

multiplier : (ℕ × ℕ) → (ℕ × ℕ)
multiplier (size , repeat) = (size ,_) ∘ sum ∘ List.map (λ n → 10 ^ (n * size)) $ range (0 , repeat ∸ 1)

numsOfDigits : ℕ → List ℕ
numsOfDigits d = range (minOfDigits d , maxOfDigits d)

numsOfDigitsUpTo : ℕ → (ℕ × ℕ) → List ℕ
numsOfDigitsUpTo maxBound (size , multiplier) =
  List.takeWhileᵇ (_≤ᵇ maxBound) ∘ List.map (multiplier *_) $ numsOfDigits size

_∈_ : ℕ → (ℕ × ℕ) → Bool
n ∈ (low , high) = (low ≤ᵇ n) ∧ (n ≤ᵇ high)

part2 : List (ℕ × ℕ) → ℕ
part2 instrs = let maxNum = Extrema.max zero $ List.map proj₂ instrs
                   minNum = Extrema.min 1_000 $ List.map proj₁ instrs
                   digits = numDigits maxNum
                   multipliers = List.map multiplier (generate (suc (digits ∸ 1)))
                   wrongNums = List.concatMap (numsOfDigitsUpTo maxNum) multipliers
                   wrongIds = List.deduplicateᵇ (_≡ᵇ_) $ List.filterᵇ (λ n → any (λ r → n ∈ r) instrs) wrongNums
               in sum wrongIds

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day02.txt"
  let instrs = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ NatShow.show $ part1 instrs

  putStrLn "Part 2:"
  putStrLn ∘ NatShow.show $ part2 instrs
