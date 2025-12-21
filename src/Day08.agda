module Day08 where

open import IO
open import Function
open import Data.Bool using (Bool; not; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Char using (_==_)
open import Data.Integer using (ℤ; +_; _-_; _^_; _+_)
open import Data.List using 
  (List; _∷_; []; map; length; zip; upTo; catMaybes; _++_; head; take; foldr; deduplicate; reverse; drop)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; suc; _∸_; _*_; _≟_; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Nat.ListAction using (product)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to map×)
open import Data.String using (String; lines; wordsByᵇ; toList)

open import Data.List.Membership.DecPropositional (_≟_) using (_∈?_)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Data.Nat.Properties using (≤-decTotalOrder)
open import Relation.Binary using (DecTotalOrder)

import Data.Tree.AVL.Sets (<-strictTotalOrder) as Set
import Data.Tree.AVL.Map (<-strictTotalOrder) as Map
open import Data.List.Sort ≤-decTotalOrder using (sort)

module UF where
  record UF : Set where
    constructor mkUF
    pattern
    field
      parentOf : Map.Map ℕ
      numComps : ℕ

  initialize : List ℕ → UF
  initialize vs = mkUF (Map.fromList (map (λ v → v , v) vs)) (length vs)

  {-# TERMINATING #-}
  find : UF → ℕ → UF × ℕ
  find (mkUF parentOf numComps) node =
    let parent = fromMaybe 0 (Map.lookup parentOf node)
    in if parent ≡ᵇ node
        then mkUF parentOf numComps , node
        else find (mkUF parentOf numComps) parent

  addEdge : UF → (ℕ × ℕ) → UF
  addEdge uf (x , y) =
    let (uf₁ , rootX ) = find uf x
        (uf₂ , rootY ) = find uf y
    in if rootX ≡ᵇ rootY
        then uf
        else mkUF (Map.insert rootX rootY (UF.parentOf uf)) -- (λ v → if v ≡ᵇ rootX then rootY else (UF.parentOf uf v))
                  (UF.numComps uf ∸ 1)

  fullyConnected? : UF → Bool
  fullyConnected? (mkUF _ numComps) = numComps ≡ᵇ 1

record Point : Set where
  constructor ⟨_,_,_⟩
  field
    x y z : ℕ

parse : String → List Point
parse = catMaybes ∘ map parseCoord ∘ lines
  where
    buildCoord : List (Maybe ℕ) → Maybe Point
    buildCoord (just x ∷ just y ∷ just z ∷ []) = just ⟨ x , y , z ⟩
    buildCoord _ = nothing

    parseCoord : String → Maybe Point
    parseCoord = buildCoord ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)

∣_,_∣² : Point → Point → ℕ
∣ ⟨ x₁ , y₁ , z₁ ⟩ , ⟨ x₂ , y₂ , z₂ ⟩ ∣² =
  let x₁ = + x₁
      x₂ = + x₂
      y₁ = + y₁
      y₂ = + y₂
      z₁ = + z₁
      z₂ = + z₂
  in toℕ $ (x₂ - x₁) ^ 2 + (y₂ - y₁) ^ 2 + (z₂ - z₁) ^ 2
  where
    toℕ : ℤ → ℕ
    toℕ (+ n) = n
    toℕ _ = 0


zipFrom : {A : Set} → ℕ → List A → List (ℕ × A)
zipFrom s xs = zip (map (s +ℕ_) (upTo (length xs))) xs

distances : List Point → ℕ → List ((ℕ × ℕ) × ℕ)
distances [] _ = []
distances (p ∷ ps) i = map (λ { (j , p′) → (i , j) , ∣ p , p′ ∣² }) (zipFrom (suc i) ps) ++ distances ps (suc i)

pair-DTO : ∀ {A : Set} → DecTotalOrder _ _ _
pair-DTO {A} = decTotalOrder ≤-decTotalOrder (proj₂ {_} {_} {A})
  where open import Relation.Binary.Construct.On using (decTotalOrder)

sortByDists : List ((ℕ × ℕ) × ℕ) → List ((ℕ × ℕ) × ℕ)
sortByDists = sortProj₂
  where open import Data.List.Sort (pair-DTO) renaming (sort to sortProj₂)

inAnyComp : ℕ → List (Set.⟨Set⟩) → Bool
inAnyComp v = any (Set.member v)

verticesFromEdges : List (ℕ × ℕ) → List ℕ
verticesFromEdges [] = []
verticesFromEdges ((v₁ , v₂) ∷ xs) = v₁ ∷ v₂ ∷ verticesFromEdges xs

neighbours : ℕ → List (ℕ × ℕ) → List ℕ
neighbours n [] = []
neighbours n ((v₁ , v₂) ∷ vs) with n ≟ v₁ | n ≟ v₂
... | yes _ | _ = v₂ ∷ neighbours n vs
... | _ | yes _ = v₁ ∷ neighbours n vs
... | _ | _ = neighbours n vs

neighs : List (ℕ × ℕ) → Map.Map (List ℕ) → Map.Map (List ℕ)
neighs [] ns = ns
neighs ((v₁ , v₂) ∷ es) ns = neighs es (Map.insertWith v₁ (go v₂) (Map.insertWith v₂ (go v₁) ns))
  where
    go : ℕ → Maybe (List ℕ) → List ℕ
    go v (just l) = if (any (⌊_⌋ ∘ (v ≟_)) l) then l else (v ∷ l)
    go v nothing = v ∷ []

{-# TERMINATING #-}
reachable : ℕ → List (ℕ × ℕ) → Set.⟨Set⟩ → Set.⟨Set⟩
reachable from edges visited =
  if Set.member from visited
    then visited
    else foldr (λ n acc → reachable n edges acc) (Set.insert from visited) (neighbours from edges)

connComps : List ℕ → List (ℕ × ℕ) → List (Set.⟨Set⟩) → List (Set.⟨Set⟩)
connComps [] edges comps = comps
connComps (v ∷ vs) edges comps =
  if (inAnyComp v comps)
    then connComps vs edges comps
    else connComps vs edges ((reachable v edges Set.empty) ∷ comps)

part1 : List Point → ℕ → ℕ
part1 points numEdges =
  let dists = sortByDists $ distances points 0
      edges = map proj₁ ∘ take numEdges $ dists
      vertices = deduplicate _≟_ $ verticesFromEdges edges
      comps = connComps vertices edges []
      compsSizes = reverse ∘ sort ∘ map Set.size $ comps
  in product ∘ take 3 $ compsSizes

mkFullyConnected : List (ℕ × ℕ) → UF.UF → Maybe (ℕ × ℕ)
mkFullyConnected [] uf = nothing
mkFullyConnected (e ∷ es) uf =
  let uf′ = UF.addEdge uf e
  in if UF.fullyConnected? uf′ then (just e) else (mkFullyConnected es uf′)

lookup : {A : Set} → List A → ℕ → Maybe A
lookup xs n = head (drop n xs)

part2 : List Point → ℕ
part2 points =
  let dists = sortByDists (distances points 0)
      edges = map proj₁ dists
      vertices = deduplicate _≟_ (verticesFromEdges edges)
      init = UF.initialize vertices
      vsIdx = fromMaybe (0 , 0) $ mkFullyConnected edges init
      getXCoord = fromMaybe 0 ∘ mapMaybe (Point.x) ∘ (lookup points)
      (x₁ , x₂) = map× getXCoord getXCoord vsIdx
  in x₁ * x₂

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day08.txt"
  let rows = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 rows 1000

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 rows
