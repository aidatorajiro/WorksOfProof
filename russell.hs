newtype Set x = Set (Set x -> Bool)

elements :: Set x -> Set x -> Bool
elements (Set f) = f

russell :: Set x
russell = Set (\(Set f) -> not $ f (Set f))

main :: IO ()
main = print $ russell `elements` russell
