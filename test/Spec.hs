import Lib
import Test.Hspec

main :: IO ()
main = hspec $ do
  -- describe "synth" $ do
  --   it "creates expr mappings for Unit" $ do
  --

  describe "typeInferStr" $ do
    it "Unit => TUnit" $ do
      typeInferStr Unit `shouldBe` Just "1"

    it "unbound identifer" $ do
      typeInferStr (Ident "x") `shouldBe` Nothing

    it "basic lambda" $ do
      typeInferStr (Lam "x" Unit) `shouldBe` Just "(a -> 1)"

    it "basic app" $ do
      typeInferStr (App (Lam "x" Unit) Unit) `shouldBe` Just "1"

    it "higher order lambda" $ do
      typeInferStr (Lam "f" (App (Ident "f") Unit))
        `shouldBe` Just "((1 -> a) -> a)"

    it "function compose" $ do
      typeInferStr (Lam "f" (Lam "g" (Lam "x" (App (Ident "f") (App (Ident "g") (Ident "x"))))))
        `shouldBe` Just "((a -> b) -> ((c -> a) -> (c -> b)))"

    it "bad app" $ do
      typeInferStr (App Unit Unit) `shouldBe` Nothing

    it "bad app 2" $ do
      typeInferStr (App Unit (Lam "f" (App (Ident "f") Unit)))
        `shouldBe` Nothing

    it "bad app 3" $ do
      typeInferStr (App (Lam "f" (App (Ident "f") Unit)) Unit)
        `shouldBe` Nothing

    it "self-referential type" $ do
      typeInferStr (Lam "x" (App (Ident "x") (Ident "x"))) `shouldBe` Nothing

    it "annotate unit" $ do
      typeInferStr (Anno Unit AUnit) `shouldBe` Just "1"

    it "annotate func 1" $ do
      typeInferStr (Anno (Lam "x" Unit) (ALam AUnit AUnit))
        `shouldBe` Just "(1 -> 1)"

    it "annotate func 2" $ do
      typeInferStr (Anno (Lam "x" Unit) (AForall "q" (ALam (AIdent "q") AUnit)))
        `shouldBe` Just "(a -> 1)"

    it "annotate identity" $ do
      typeInferStr (Anno (Lam "x" (Ident "x")) (AForall "q" (ALam (AIdent "q") (AIdent "q"))))
        `shouldBe` Just "(a -> a)"

    it "annotate function identity" $ do
      typeInferStr (Anno (Lam "x" (Ident "x")) (AForall "p" (AForall "q" (ALam (ALam (AIdent "p") (AIdent "q")) (ALam (AIdent "p") (AIdent "q"))))))
        `shouldBe` Just "((a -> b) -> (a -> b))"

    it "bad annotate identity" $ do
      typeInferStr (Anno (Lam "x" (Ident "x")) (AForall "q" (ALam (AIdent "q") AUnit)))
        `shouldBe` Nothing

    it "variable shadowing" $ do
      typeInferStr
        (Lam "x"
          (App
            (Lam "_"
              (Anno
                (Lam "x" (Ident "x"))
                (AForall "p" (ALam (AIdent "p") (AIdent "p")))))
            (Anno (Ident "x") AUnit)))
        `shouldBe` Just "(1 -> (a -> a))"
