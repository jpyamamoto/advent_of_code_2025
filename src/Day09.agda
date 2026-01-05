module Day09 where

open import IO
open import Function
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.Char using (_==_)
open import Data.List
  using (List; _∷_; []; [_]; map; catMaybes; _++_; deduplicateᵇ; upTo; zip
        ; length; drop; head; foldr; replicate; last; concatMap; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_; _*_; _⊓′_; _⊔′_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-totalOrder; ≤-decTotalOrder; <-strictTotalOrder)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)
open import Data.String using (String; lines; wordsByᵇ)
open import Data.Tree.AVL.Sets (×-strictTotalOrder <-strictTotalOrder <-strictTotalOrder)
  using (⟨Set⟩; empty; union; member; insert; delete)
  renaming (fromList to setFromList; foldr to setFoldr)
open import Data.Tree.AVL.Map (<-strictTotalOrder) using (lookup) renaming (fromList to mapFromList)

open import Data.List.Extrema ≤-totalOrder using (max)
open import Data.List.Sort ≤-decTotalOrder using (sort)

record Compression : Set where
  field
    xs ys : List ℕ
    getXIdx getYIdx : ℕ → ℕ
    maxX maxY : ℕ

open Compression

zipWithIndex : {A : Set} → List A → List (A × ℕ)
zipWithIndex xs = zip xs (upTo (length xs))

parse : String → List (ℕ × ℕ)
parse = catMaybes ∘ map parsePoint ∘ lines
  where
    buildPoint : List (Maybe ℕ) → Maybe (ℕ × ℕ)
    buildPoint (just x ∷ just y ∷ []) = just (x , y)
    buildPoint _ = nothing

    parsePoint : String → Maybe (ℕ × ℕ)
    parsePoint = buildPoint ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)

subsets : ∀ {A : Set} → List A → List (A × A)
subsets [] = []
subsets (x ∷ xs) = map (x ,_) xs ++ subsets xs

maxArea : ((ℕ × ℕ) × (ℕ × ℕ) → Bool) → List (ℕ × ℕ) → ℕ
maxArea guard = max zero ∘ map dist ∘ filterᵇ guard ∘ subsets
  where
    diff : ℕ → ℕ → ℕ
    diff x y = (suc (x ⊔′ y)) ∸ (x ⊓′ y)

    dist : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ
    dist ((x₁ , y₁) , (x₂ , y₂)) = (diff x₁ x₂) * (diff y₁ y₂)

part1 : List (ℕ × ℕ) → ℕ
part1 = maxArea (const true)

compress : List (ℕ × ℕ) → Compression
compress points =
  let xs = sort ∘ deduplicateᵇ _≡ᵇ_ ∘ map proj₁ $ points
      ys = sort ∘ deduplicateᵇ _≡ᵇ_ ∘ map proj₂ $ points
      maxX = suc (fromMaybe 0 $ last xs)
      maxY = suc (fromMaybe 0 $ last ys)
      xs′ = ((fromMaybe 0 $ head xs) ∸ 1) ∷ xs ++ [ maxX ]
      ys′ = ((fromMaybe 0 $ head ys) ∸ 1) ∷ ys ++ [ maxY ]
  in case (mapFromList (zipWithIndex xs′) , mapFromList (zipWithIndex ys′)) of λ where
      (xIdx , yIdx) → record
        { xs = xs′
        ; ys = ys′
        ; getXIdx = fromMaybe 0 ∘ lookup xIdx
        ; getYIdx = fromMaybe 0 ∘ lookup yIdx
        ; maxX = maxX
        ; maxY = maxY
        }

edges : List (ℕ × ℕ) → List ((ℕ × ℕ) × (ℕ × ℕ))
edges xs = zip xs (drop 1 xs ++ [ (fromMaybe (0 , 0) $ head xs) ])

∣_,_∣ : ℕ → ℕ → ℕ
∣ n , m ∣ = if n ≤ᵇ m then m ∸ n else n ∸ m

bound : List (ℕ × ℕ) → Compression → ⟨Set⟩
bound points κ = foldr putSegment empty (edges points)
  where
    putSegment : ((ℕ × ℕ) × (ℕ × ℕ)) → ⟨Set⟩ → ⟨Set⟩
    putSegment ((x₁ , y₁) , (x₂ , y₂)) s with x₁ ≡ᵇ x₂
    ... | true = 
      let y₁′ = getYIdx κ y₁
          y₂′ = getYIdx κ y₂
          x′  = getXIdx κ x₁
          gap = suc ∣ y₁′ , y₂′ ∣
          segment = zip (replicate gap x′) (map ((y₁′ ⊓′ y₂′) +_) (upTo gap))
       in union s (setFromList segment)
    ... | false = 
      let x₁′ = getXIdx κ x₁
          x₂′ = getXIdx κ x₂
          y′  = getYIdx κ y₁
          gap = suc ∣ x₁′ , x₂′ ∣
          segment = zip (map ((x₁′ ⊓′ x₂′) +_) (upTo gap)) (replicate gap y′)
       in union s (setFromList segment)

{-# TERMINATING #-}
floodFill : ⟨Set⟩ → List (ℕ × ℕ) → ⟨Set⟩ → (ℕ × ℕ) → ⟨Set⟩
floodFill visited [] _ _ = visited
floodFill visited ((x , y) ∷ ps) boundary maxCoords with member (x , y) visited
... | true = floodFill visited ps boundary maxCoords
... | false with member (x , y) boundary
... | true = floodFill visited ps boundary maxCoords
... | false = floodFill (insert (x , y) visited) (neighs (x , y) maxCoords ++ ps) boundary maxCoords
  where
    neighs : ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ)
    neighs (x , y) (maxX , maxY) =
      (x ∸ 1 , y) ∷ ((suc x) ⊓′ maxX , y) ∷ (x , y ∸ 1) ∷ (x , suc y ⊓′ maxY) ∷ []

allCoordsInRect : (ℕ × ℕ) × (ℕ × ℕ) → List (ℕ × ℕ)
allCoordsInRect ((x₁ , y₁) , (x₂ , y₂)) =
  let x₁′ = x₁ ⊓′ x₂
      x₂′ = x₁ ⊔′ x₂
      y₁′ = y₁ ⊓′ y₂
      y₂′ = y₁ ⊔′ y₂
      maxX = suc (x₂′ ∸ x₁′)
      maxY = suc (y₂′ ∸ y₁′)
   in concatMap (λ y → map (_, y) (map (x₁′ +_) (upTo maxX))) (map (y₁′ +_) (upTo maxY))

getOutside : ⟨Set⟩ → Compression → ⟨Set⟩
getOutside boundary κ = floodFill empty [ (0 , 0) ] boundary (getXIdx κ (maxX κ) , getYIdx κ (maxY κ))

getInside : ⟨Set⟩ → Compression → ⟨Set⟩
getInside boundary κ =
  let maxX = getXIdx κ (maxX κ)
      maxY = getYIdx κ (maxY κ)
      allCoords = setFromList $ allCoordsInRect ((0 , 0) , (maxX , maxY))
      outside = getOutside boundary κ
   in setFoldr delete allCoords outside

-- This can be improved with a summed-area table,
-- I might come back later and make it more efficient.
part2 : List (ℕ × ℕ) → ℕ
part2 points =
  case compress points of λ where
    κ → case bound points κ of λ where
      boundary → case getInside boundary κ of λ where
        inside → maxArea (validRect κ inside) points
  where
    validRect : Compression → ⟨Set⟩ → (ℕ × ℕ) × (ℕ × ℕ) → Bool
    validRect κ inside ((x₁ , y₁) , (x₂ , y₂)) =
      all (λ c → member c inside)
          (allCoordsInRect ((getXIdx κ x₁ , getYIdx κ y₁) , getXIdx κ x₂ , getYIdx κ y₂))

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day09.txt"
  let points = parse contents
  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 points

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 points
