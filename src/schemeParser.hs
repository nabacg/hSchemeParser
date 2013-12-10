 {-# LANGUAGE ExistentialQuantification #-} 
import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment
import Control.Monad
import Control.Monad.Error
import System.IO
import Data.IORef

data LispVal = Atom String
				| List [LispVal]
				| DottedList [LispVal] LispVal
				| Number Integer
				| String String
				| Bool Bool
				| PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
				| IOFunc ([LispVal] -> IOThrowsError LispVal)
				| Port Handle				
				| Func {params :: [String], vararg :: (Maybe String), 
						body :: [LispVal], closure :: Env}

data LispError = NumArgs Integer [LispVal]
                 | TypeMismatch String LispVal
                 | Parser ParseError
                 | BadSpecialForm String LispVal
                 | NotFunction String String
                 | UnboundVar String String
                 | Default String
--requires {-# LANGUAGE ExistentialQuantification #-} 			 
-- allows to use any unpacker if it satisfies the Eq typeclass
data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)				 
                   
instance Show LispVal where show = showVal
instance Show LispError where show = showError 
instance Error LispError where
  noMsg = Default "An error has occurred"
  strMsg = Default

type ThrowsError = Either LispError
type Env = IORef [(String, IORef LispVal)]

trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val
  
showError :: LispError -> String
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func) = message ++ ": " ++ show func
showError (NumArgs expected found) = "Expected " ++ show expected
                                     ++ " args; found values " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected
                                          ++ ", found " ++ show found
showError (Parser parseErr) = "Parse error at " ++ show parseErr



symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"
	
spaces :: Parser ()
spaces = skipMany1 space	
				
parseString :: Parser LispVal
parseString = do 
				char '"'
				x <- many (noneOf "\"")
				char '"'
				return $ String x				
				
parseAtom :: Parser LispVal
parseAtom = do
			first <- letter <|> symbol
			rest <- many (letter <|> digit <|> symbol)
			let atom = first:rest
			return $ case atom of
						"#t" -> Bool True
						"#f" -> Bool False
						_ 	 -> Atom atom
							
parseNumber :: Parser LispVal
parseNumber = liftM (Number . read) $ many1 digit	


		
parseList :: Parser LispVal
parseList = liftM List (sepBy parseExpr spaces)

parseDottedList :: Parser LispVal
parseDottedList = do
				head <- endBy parseExpr spaces
				tail <- char '.' >> spaces >> parseExpr
				return $ DottedList head tail
				
parseQuoted :: Parser LispVal
parseQuoted = do
			char '\''
			x <- parseExpr
			return $ List [Atom "quote", x]
			
parseExpr :: Parser LispVal
parseExpr = parseAtom 
		<|> parseString
		<|> parseNumber
		<|> parseQuoted
		<|> do
			char '('
			x <- try parseList <|> parseDottedList
			char ')'
			return x
			
readOrThrow :: Parser a -> String -> ThrowsError a
readOrThrow parser input = case parse parser "lisp" input of
						Left err -> throwError $ Parser err
						Right val -> return val
		
readExpr :: String -> ThrowsError LispVal
readExpr = readOrThrow parseExpr
readExprList = readOrThrow (endBy parseExpr spaces)
--readExpr input = case parse parseExpr "lisp" input of
--	Left err -> throwError $ Parser err  
--	Right val -> return val
	
showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Atom name) = name
showVal (Number n) = show n
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (List xs) = "(" ++ unwordsList xs ++ ")"
showVal (DottedList head tail) = "(" ++ unwordsList head ++ " . " ++ showVal tail ++ ")"
showVal (PrimitiveFunc _) = "<primitive>"
showVal (IOFunc _) = "<IO primitive>"
showVal (Port _) = "<IO port>"
showVal (Func {params = args, vararg = varargs, body = body, closure = env}) = 
																		"(lambda (" ++ unwords (map show args) ++ 
																			(case varargs of
																					Nothing -> ""
																					Just arg -> " . " ++ arg) ++ ") ...)"

unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

--------------------------------- evaluator -----------------------------------------

eval :: Env -> LispVal -> IOThrowsError LispVal
eval env val@(String _) = return val
eval env val@(Number _) = return val
eval env val@(Bool _) = return val
eval env (Atom id) = getVar env id
eval env (List [Atom "quote", val]) = return val
eval env (List (Atom "quote" : tail)) = return $ List tail
eval env (List [Atom "load", String filename]) = load filename >>= liftM last . mapM (eval env)
eval env (List [Atom "if", pred, clause, elseClause]) = do 	
													res <- eval env pred
													case res of 
														Bool False -> eval env elseClause
														otherwise -> eval env clause
eval env (List [Atom "define", (Atom name), form]) = eval env form >>= defineVar env name
eval env (List (Atom "define" : List (Atom var : params) : body)) = makeNormalFunc env params body >>= defineVar env var
eval env (List (Atom "define" : DottedList (Atom var : params) varargs : body)) = 
													makeVarargs varargs env params body >>= defineVar env var
eval env (List (Atom "lambda" : List params : body)) = makeNormalFunc env params body
eval env (List (Atom "lambda" : DottedList params varargs : body)) =
														makeVarargs varargs env params body
eval env (List (Atom "lambda" : varargs@(Atom _) : body)) =
														makeVarargs varargs env [] body
eval env (List [Atom "set!", Atom name, form]) = eval env form >>= setVar env name
eval env (List (Atom "cond" : first : rest)) = evalCondClause env first rest
eval env (List (func : args)) = do
									func <- eval env func
									argVals <- mapM (eval env) args 
									apply func argVals
eval env badForm = throwError $ BadSpecialForm "Unrecognized special form " badForm

evalCondClause :: Env -> LispVal -> [LispVal] -> IOThrowsError LispVal
evalCondClause env (List (Atom "else" : [stmt])) _ = eval env stmt
evalCondClause env (List (pred : stmt : [])) rest = do
										result <- eval env pred
										case result of
											Bool True -> eval env stmt
											otherwise -> evalCondClause env (head rest) (tail rest)
											

										

makeFunc varargs env params body = return $ Func (map showVal params) varargs body env
makeNormalFunc = makeFunc Nothing
makeVarargs = makeFunc . Just . showVal
									
--------------------------------- evaluator -----------------------------------------										

-- eval (List ((Atom "+"):args)) = Number $ sum (map unwrappNum args)
-- eval (List ((Atom "*"):args)) = Number $ product (map unwrappNum args)
-- unwrappNum :: LispVal -> Integer
-- unwrappNum (Number n) = n

apply :: LispVal -> [LispVal] -> IOThrowsError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (IOFunc func) args = func args
apply (Func params varargs body closure) args = 
	if num params /= num args && varargs == Nothing
		then throwError $ NumArgs (num params) args
		else (liftIO $ bindVars closure $ zip params args) >>= bindVarArgs varargs >>= evalBody
	where
		remainingArgs = drop (length params) args
		num = toInteger . length
		evalBody env = liftM last $ mapM (eval env) body
		bindVarArgs arg env = case arg of
			Just argName -> liftIO $ bindVars env [(argName, List $ remainingArgs)]
			Nothing -> return env
			
	
			
ioPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal)]
ioPrimitives = [("apply", applyProc),
				("open-input-file", makePort ReadMode),
				("open-output-file", makePort WriteMode),
				("close-input-port", closePort),
				("close-output-port", closePort),
				("read", readProc),
				("write", writeProc),
				("read-contents", readContents),
				("read-all", readAll)]

makePort :: IOMode -> [LispVal] -> IOThrowsError LispVal
makePort mode [String filename] = liftM Port $ liftIO $ openFile filename mode				

closePort :: [LispVal] -> IOThrowsError LispVal
closePort [Port port] = liftIO $ hClose port >> (return $ Bool True)
closePort _ = return $ Bool False

readProc :: [LispVal] -> IOThrowsError LispVal
readProc [] = readProc [Port stdin]
readProc [Port port] = (liftIO $ hGetLine port) >>= liftThrows . readExpr

writeProc :: [LispVal] -> IOThrowsError LispVal
writeProc [obj] = writeProc [obj, Port stdout]
writeProc [obj, Port port] = liftIO $ hPrint port obj >> (return $ Bool True)

readContents :: [LispVal] -> IOThrowsError LispVal
readContents [String filename] = liftM String $ liftIO $ readFile filename

load :: String -> IOThrowsError [LispVal]
load filename = (liftIO $ readFile filename) >>= liftThrows . readExprList

readAll :: [LispVal] -> IOThrowsError LispVal
readAll [String filename] = liftM List $ load filename

applyProc :: [LispVal] -> IOThrowsError LispVal
applyProc [func, List args] = apply func args
applyProc (func : args) = apply func args		

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("mod", numericBinop mod),
              ("quotient", numericBinop quot),
              ("remainder", numericBinop rem),
              ("string?", unaryOp symbolp),
              ("number?", unaryOp numberp),
              ("list?", unaryOp listp),
              ("pair?", unaryOp pairp),
              ("symbol?", unaryOp symbolp),
              ("symbol->string", unaryOp symbol2String),
              ("string->symbol", unaryOp string2Symbol),
			  ("=", numBoolBinop (==)),
			  ("<", numBoolBinop (<)),
			  (">", numBoolBinop (>)),
			  ("/=", numBoolBinop (>=)),
			  (">=", numBoolBinop (>=)),
			  ("<=", numBoolBinop (<=)),
			  ("&&", boolBoolBinop (&&)),
			  ("||", boolBoolBinop (||)),
			  ("string=?", strBoolBinop (==)),
			  ("string<?", strBoolBinop (<)),
			  ("string>?", strBoolBinop (>)),
			  ("string<=?", strBoolBinop (<=)),
			  ("string>=?", strBoolBinop (>=)),
			  ("car", car),
			  ("cdr", cdr),
			  ("cons", cons),
			  ("eq?", eqv),
			  ("eqv?", eqv),
			  ("equal?", equal)]
			  
primitiveBindings :: IO Env
primitiveBindings = nullEnv >>= (flip bindVars $ map (makeFunc PrimitiveFunc) primitives 
												++ map (makeFunc IOFunc) ioPrimitives)
				where makeFunc constructor (var, func) = (var, constructor func)

unaryOp :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = return $ f v

symbol2String :: LispVal -> LispVal
symbol2String (Atom s) = String s
symbol2String _ = String ""

string2Symbol :: LispVal -> LispVal
string2Symbol (String s) = Atom s
string2Symbol _ = Atom ""

symbolp, numberp, listp, pairp :: LispVal -> LispVal
symbolp (Atom _) = Bool True
symbolp _ = Bool False
numberp (Number _) = Bool True
numberp _ = Bool False
listp (List _) = Bool True
listp _ = Bool False
pairp (List _) = Bool True
pairp (DottedList _ _) = Bool True
pairp _ = Bool False

numBoolBinop = boolBinop unpackNum
strBoolBinop = boolBinop unpackString
boolBoolBinop = boolBinop unpackBool

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpackFunc op args =  if length args /= 2
								then throwError $ NumArgs 2 args
								else do 
										left <- unpackFunc $ args !! 0
										right <- unpackFunc $ args !! 1
										return $ Bool $ left `op` right

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum notNum  = throwError $ TypeMismatch "number" notNum										
										
unpackString :: LispVal -> ThrowsError String
unpackString (String s) = return s
unpackString (Number n) = return $ show n
unpackString (Bool b) = return $ show b
unpackString notString = throwError $ TypeMismatch "string" notString										

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool			  
			  
numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params = mapM unpackNum params >>= return . Number . foldl1 op 

car :: [LispVal] -> ThrowsError LispVal
car [List (x : xs)] = return x
car [DottedList (x : xs) _] = return x
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x : xs)] = return $ List xs
cdr [DottedList [_] x] = return x
cdr [DottedList (_ : x) xs] = return $ DottedList x xs
cdr [badArg] = throwError $ TypeMismatch "pair" badArg
cdr badArgList = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []] = return $ List [x1]
cons [x1, List xs] = return $ List $ x1 : xs
cons [x1, DottedList xs xlast] = return $ DottedList (x1 : xs) xlast
cons [x1, x2] = return $ DottedList [x1] x2
cons badArgList = throwError $ NumArgs 1 badArgList


eqv :: [LispVal] -> ThrowsError LispVal
eqv [(Bool arg1), (Bool arg2)] = return $ Bool $ arg1 == arg2
eqv [(String arg1), (String arg2)] = return $ Bool $ arg1 == arg2
eqv [(Number arg1), (Number arg2)] = return $ Bool $ arg1 == arg2
eqv [(Atom arg1), (Atom arg2)] = return $ Bool $ arg1 == arg2
eqv [(DottedList xs x), (DottedList ys y)] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
eqv [(List xs), (List ys)] = return $ Bool $ (length xs == length ys)&&
										(all eqvPair $ zip xs ys)
							where eqvPair (x, y) = case equal [x,y] of
									Left err -> False
									Right (Bool val) -> val
eqv [_, _] = return $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList									

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = do 
											unpacked1 <- unpacker arg1
											unpacked2 <- unpacker arg2
											return $ unpacked1 == unpacked2 
									`catchError` (const $ return False)
	
equal :: [LispVal] -> ThrowsError LispVal
equal [arg1, arg2] = do
		primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2)
						[AnyUnpacker unpackNum, AnyUnpacker unpackString, AnyUnpacker unpackBool]
		eqvEquals <- eqv [arg1, arg2]
		return $ Bool $ (primitiveEquals || let (Bool x) = eqvEquals in x)
equal badArgList = throwError $ NumArgs 2 badArgList		
-- :main "(a '(dotted . list) test)"
-- :main "(4124 23 (12 (test)) aa)"
-- :main "(+ 23221 1 123 123 1111111)"
-- :main "(+ 5 (* 2 (* 200 2)))"
-- main = getArgs >>= print . eval . readExpr . head



-------------------------------- Variables -------------------------------- 

nullEnv :: IO Env
nullEnv = newIORef []

type IOThrowsError = ErrorT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = runErrorT (trapError action) >>= return . extractValue

isBound :: Env -> String -> IO Bool
isBound envRef varName = readIORef envRef >>= return . maybe False (const True) . lookup varName

getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var = do
					env <- liftIO $ readIORef envRef 
					maybe (throwError $ UnboundVar "Getting an unbound variable" var)
						(liftIO . readIORef)
						(lookup var env)
						
setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value = do 
						env <- liftIO $ readIORef envRef
						maybe (throwError $ UnboundVar "Setting an unbound variable" var)
							(liftIO . (flip writeIORef value))
							(lookup var env)
						return value
						
defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value = do
						alreadyDefined <- liftIO $ isBound envRef var
						if alreadyDefined
							then setVar envRef var value >> return value
							else liftIO $ do
								valueRef <- newIORef value
								env <- readIORef envRef
								writeIORef envRef ((var, valueRef) : env)
								return value
								
bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef bidings = readIORef envRef >>= extendEnv bidings >>= newIORef 
							where 
								extendEnv bindings env = liftM (++ env) (mapM addBinding bindings)
								addBinding (var, value) = do 
															ref <- newIORef value
															return (var, ref)
								
						
-------------------------------- Variables -------------------------------- 
-------------------------------- REPL --------------------------------
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ (liftThrows $ readExpr expr ) >>= eval env

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m()) -> m ()
until_ pred prompt action = do
	result <- prompt
	if pred result
		then return ()
		else action result >> until_ pred prompt action

runOne :: [String] -> IO ()
runOne args = do
			env <- primitiveBindings >>= flip bindVars [("args", List $ map String $ drop 1 args)] 
			(runIOThrows $ liftM show $ eval env (List [Atom "load", String (args !! 0)]))
				>>= hPutStrLn stderr
		
runRepl :: IO ()
runRepl = primitiveBindings >>= until_ (== "quit") (readPrompt "Lisp>>> ") . evalAndPrint


-------------------------------- REPL --------------------------------
-- (define my-count (counter 111))
--(define (counter inc) (lambda (x) (set! inc (+ x inc)) inc))
-- (my-count 1)
main = do 
		args <- getArgs
		if null args 
			then runRepl 
			else runOne $ args
