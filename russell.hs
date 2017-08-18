newtype Set x = Set (Set x -> Bool)

elements :: Set x -> Set x -> Bool
elements (Set f) = f

russell :: Set x
russell = Set (\e -> not $ e `elements` e)

main :: IO ()
main = print $ russell `elements` russell
