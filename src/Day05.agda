module Day05 where

open import IO
open import Function
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Char using () renaming (_==_ to _C=_)
open import Data.List
  using (List; _∷_; []; filterᵇ; map; length; spanᵇ; drop; catMaybes)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _⊔′_; _∸_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤-decTotalOrder)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_; map₁; map₂)
open import Data.Product.Relation.Binary.Lex.NonStrict using (×-decTotalOrder)
open import Data.String using (String; lines; _==_; wordsByᵇ)

open import Data.List.Sort (×-decTotalOrder ≤-decTotalOrder ≤-decTotalOrder)
  using (sort)

record Range : Set where
  constructor [_,_]
  field
    min : ℕ
    max : ℕ

partitionLines : String → List String × List String
partitionLines = map₂ (drop 1) ∘ spanᵇ (not ∘ ("" ==_)) ∘ lines

parseNums : List String → List ℕ
parseNums = catMaybes ∘ map (readMaybe 10)

parseRanges : List String → List Range
parseRanges = catMaybes ∘ map parseRange
  where
    parseRange : String → Maybe Range
    parseRange str with wordsByᵇ ('-' C=_) str
    ... | left ∷ right ∷ [] with readMaybe 10 left | readMaybe 10 right
    ... | just l | just r = just [ l , r ]
    ... | _      | _      = nothing
    parseRange _ | _    = nothing

parse : String → List Range × List ℕ
parse = (map₁ parseRanges) ∘ (map₂ parseNums) ∘ partitionLines

{-# TERMINATING #-}
mergeRanges : List Range → List Range
mergeRanges [] = []
mergeRanges (r ∷ []) = r ∷ []
mergeRanges ([ l₁ , r₁ ] ∷ [ l₂ , r₂ ] ∷ xs) with (l₂ ≤ᵇ r₁)
... | true  = mergeRanges ([ l₁ , r₁ ⊔′ r₂ ] ∷ xs)
... | false = [ l₁ , r₁ ] ∷ mergeRanges ([ l₂ , r₂ ] ∷ xs)

_∈_ : ℕ → Range → Bool
n ∈ [ l , r ] = (l ≤ᵇ n) ∧ (n ≤ᵇ r)

getFreshIds : List Range → List ℕ → List ℕ
getFreshIds ranges ids = filterᵇ (λ i → any (λ r → i ∈ r) ranges) ids

sortRanges : List Range → List Range
sortRanges = map (toRange) ∘ sort ∘ map (fromRange)
  where
    fromRange : Range → ℕ × ℕ
    fromRange [ min , max ] = min , max

    toRange : ℕ × ℕ → Range
    toRange (min , max) = [ min , max ]

∣_∣ : Range → ℕ
∣ [ min , max ] ∣ = suc (max ∸ min)

part1 : List Range → List ℕ → ℕ
part1 = (length ∘_) ∘ getFreshIds ∘ mergeRanges ∘ sortRanges

part2 : List Range → ℕ
part2 = sum ∘ map ∣_∣ ∘ mergeRanges ∘ sortRanges

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day05.txt"
  let (ranges , ids) = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 ranges ids

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 ranges
