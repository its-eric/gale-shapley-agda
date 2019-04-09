open import Data.Nat

data MensPref : Set where
  woman : ℕ → MensPref
  node  : MensPref → MensPref → MensPref
  man   : ℕ → MensPref → MensPref → MensPref

-- [(1, [2,1]), (2, [1,2])]
ex : MensPref
ex =
  node
    (man 1
       (woman 2)
       (woman 1))
    (man 2
       (woman 1)
       (woman 2))

-- [(1, [2,3,1]), (2, [1,2,3]), (3, [2,1,3])]
ex' : MensPref
ex' =
  node
    (man 1
       (woman 2)
       (man 1
         (woman 3)
         (woman 1)))
    (node
      (man 2
         (woman 1)
         (man 2
           (woman 2)
           (woman 3)))
      (man 3
         (woman 2)
         (man 3
           (woman 1)
           (woman 3))))

-- exercises: write conversion from [([])] to MensPref
-- write the step function
