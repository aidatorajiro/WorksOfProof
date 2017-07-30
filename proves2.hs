{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- [定義]
data Not p

-- [公理]
-- 排中律
class Classic where
    classic :: Either p (Not p)

-- pで矛盾が導かれるならばpでない、pでないならばpで矛盾が導かれる
class Contradiction where
    cton :: (forall q. p -> q) -> Not p
    ntoc :: Not p -> (forall q. p -> q)

-- [証明]
-- 三段論法
syllogism :: (p -> q) -> (q -> r) -> (p -> r)
syllogism h1 h2 = h2 . h1

-- 交換法則（かつ）
commutativeLawAnd :: (p, q) -> (q, p)
commutativeLawAnd (p, q) = (q, p)

-- 交換法則（または）
commutativeLawOr :: Either p q -> Either q p
commutativeLawOr (Left  p) = Right p
commutativeLawOr (Right q) = Left  q

-- 結合法則
associativeLaw :: ((p -> q) -> r) -> (p -> (q -> r))
associativeLaw h = const $ h . const

-- P -> Pでない -> Q
bomb :: Contradiction => p -> Not p -> q
bomb p np = (ntoc np) p

-- (Pかつ(Pでない))ならばQ
bombAnd :: Contradiction => (p, Not p) -> q
bombAnd (p, np) = bomb p np

-- ド・モルガンの法則
deMorgan :: Contradiction => (Not p, Not q) -> Not (Either p q)
deMorgan (np, nq) = cton (\pq ->
    case pq of
        Left  p -> bomb p np
        Right q -> bomb q nq )

-- 二重否定法則
pnnp :: Contradiction => p -> Not (Not p)
pnnp p = cton $ bomb p

nnpp :: (Contradiction, Classic) => Not (Not p) -> p
nnpp nnp = case classic of
    Left  p  -> p
    Right np -> bomb np nnp

-- 対偶
contraposition1 :: Contradiction => (p -> q) -> (Not q -> Not p)
contraposition1 h nq = cton (\p -> bomb (h p) nq)

contraposition2 :: (Contradiction, Classic) => (Not q -> Not p) -> (p -> q)
contraposition2 h p = nnpp $ (contraposition1 h) (pnnp p)

-- パースの法則
peirce_lemma1 :: (Contradiction, Classic) => ((p -> q) -> p) -> ((Not q -> Not p) -> p)
peirce_lemma1 x y = x (contraposition2 y)

peirce_lemma2 :: (Contradiction, Classic) => (Not p -> p) -> p
peirce_lemma2 x = either id x classic

peirce :: (Contradiction, Classic) => ((p -> q) -> p) -> p
peirce h =
    peirce_lemma2
    (
        const
        $
        either
        (h . const)
        (peirce_lemma2 . (associativeLaw $ peirce_lemma1 h))
        classic
    )

-- なんか
prop1 :: (forall p. ((p -> q) -> q)) -> ((p -> q) -> p) -> p
prop1 h h0 = h0 $ const $ h id

main :: IO ()
main = return ()