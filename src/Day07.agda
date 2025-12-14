module Day07 where

open import IO
open import Function
open import Data.Bool using (not; if_then_else_)
open import Data.Char using (_==_)
open import Data.List using (List; _∷_; []; filterᵇ; map; length; zip; upTo)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _∸_; _+_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Show using (show)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; lines; toList)

import Data.Tree.AVL.Sets (<-strictTotalOrder) as Set
import Data.Tree.AVL.Map (<-strictTotalOrder) as Map

zipWithIndex : {A : Set} → List A → List (ℕ × A)
zipWithIndex xs = zip (upTo (length xs)) xs

parseElems : String → List ℕ
parseElems = map proj₁ ∘ filterᵇ (not ∘ ('.' ==_) ∘ proj₂) ∘ zipWithIndex ∘ toList

parse : String → ℕ × List (Set.⟨Set⟩)
parse content with lines content
... | [] = 0 , []
... | fstLine ∷ restLines with parseElems fstLine
... | initial ∷ [] = initial , map (Set.fromList ∘ parseElems) restLines
... | _ = 0 , []

runRow : Set.⟨Set⟩ → Set.⟨Set⟩ → Set.⟨Set⟩ × ℕ
runRow beams splitters = Set.foldr checkMember (Set.empty , 0) beams
  where
    checkMember : ℕ → Set.⟨Set⟩ × ℕ → Set.⟨Set⟩ × ℕ
    checkMember beam (newBeams , count) = if (Set.member beam splitters)
                                          then Set.insert (beam ∸ 1) (Set.insert (suc beam) newBeams) , suc count
                                          else (Set.insert beam newBeams , count)

runQuantumRow : Map.Map ℕ → Set.⟨Set⟩ → Map.Map ℕ
runQuantumRow beams splitters = Map.foldr splitTimelines Map.empty beams
  where
    updateCount : ℕ → Maybe ℕ → ℕ
    updateCount add (just curr) = add + curr
    updateCount default nothing = default

    setBeam : ℕ → ℕ → Map.Map ℕ → Map.Map ℕ
    setBeam beam timelines allBeams = Map.insertWith beam (updateCount timelines) allBeams

    splitTimelines : ℕ → ℕ → Map.Map ℕ → Map.Map ℕ
    splitTimelines beam count allBeams = if (Set.member beam splitters)
                                         then setBeam (beam ∸ 1) count (setBeam (suc beam) count allBeams)
                                         else setBeam beam count allBeams

part1 : Set.⟨Set⟩ → List (Set.⟨Set⟩) → ℕ → ℕ
part1 _ [] n = n
part1 beams (row ∷ rest) n with (newBeams , splits) ← runRow beams row
  = part1 newBeams rest (n + splits)

part2 : Map.Map ℕ → List (Set.⟨Set⟩) → ℕ
part2 beams [] = sum ∘ map proj₂ ∘ Map.toList $ beams
part2 beams (row ∷ rest) = part2 (runQuantumRow beams row) rest

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day07.txt"
  let (initial , rows) = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 (Set.singleton initial) rows 0

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 (Map.singleton initial 1) rows
