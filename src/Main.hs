--------------------------------------------------------------------------------
module Main where


--------------------------------------------------------------------------------
import qualified CoreSyn            as Ghc
import qualified DynFlags           as Ghc
import qualified GHC                as Ghc
import qualified GHC.Paths          as Ghc.Paths
import qualified HscTypes           as Ghc
import qualified Outputable         as Ghc
import           System.Environment (getArgs)


--------------------------------------------------------------------------------
main :: IO ()
main = do
    (filePath : _) <- getArgs
    coreProgram    <- getCoreProgram filePath
    putStrLn $ Ghc.showSDoc $ Ghc.ppr coreProgram


--------------------------------------------------------------------------------
getCoreProgram :: FilePath -> IO Ghc.CoreProgram
getCoreProgram filePath =
    Ghc.defaultErrorHandler Ghc.defaultLogAction $ do
        Ghc.runGhc (Just Ghc.Paths.libdir) $ do
            dflags <- Ghc.getSessionDynFlags
            _      <- Ghc.setSessionDynFlags dflags
            target <- Ghc.guessTarget filePath Nothing
            Ghc.setTargets [target]
            _      <- Ghc.load Ghc.LoadAllTargets
            modSum <- Ghc.getModSummary $ Ghc.mkModuleName "Main"
            p      <- Ghc.parseModule modSum
            t      <- Ghc.typecheckModule p
            d      <- Ghc.desugarModule t
            return $ Ghc.mg_binds $ Ghc.coreModule d
