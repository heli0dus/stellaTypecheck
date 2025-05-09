-- -*- haskell -*- File generated by the BNF Converter (bnfc 2.9.5).

-- Lexer definition for use with Alex 3
{
{-# OPTIONS -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -w #-}

{-# LANGUAGE PatternSynonyms #-}

module Stella.Lex where

import Prelude

import qualified Data.Bits
import Data.Char     (ord)
import Data.Function (on)
import Data.Word     (Word8)
}

-- Predefined character classes

$c = [A-Z\192-\221] # [\215]  -- capital isolatin1 letter (215 = \times) FIXME
$s = [a-z\222-\255] # [\247]  -- small   isolatin1 letter (247 = \div  ) FIXME
$l = [$c $s]         -- letter
$d = [0-9]           -- digit
$i = [$l $d _ ']     -- identifier character
$u = [. \n]          -- universal: any character

-- Symbols and non-identifier-like reserved words

@rsyms = \µ | \, | \; | \( | \) | \{ | \} | \[ | \] | \= | \: | \- \> | \= \> | \| | \< \| | \| \> | \: \= | \< | \< \= | \> | \> \= | \= \= | \! \= | \+ | \- | \* | \/ | \. | "List" \: \: "head" | "List" \: \: "isempty" | "List" \: \: "tail" | "panic" \! | "Nat" \: \: "pred" | "Nat" \: \: "iszero" | "Nat" \: \: "rec" | \&

:-

-- Line comment "//"
"//" [.]* ;

-- Block comment "/*" "*/"
\/ \* [$u # \*]* \* ([$u # [\* \/]] [$u # \*]* \* | \*)* \/ ;

-- Whitespace (skipped)
$white+ ;

-- Symbols
@rsyms
    { tok (eitherResIdent TV) }

-- token StellaIdent
(\_ | $l)([\! \- \: \? \_]| ($d | $l)) *
    { tok (eitherResIdent T_StellaIdent) }

-- token ExtensionName
\# ([\- \_]| ($d | $l)) +
    { tok (eitherResIdent T_ExtensionName) }

-- token MemoryAddress
\< 0 x ([A B C D E F a b c d e f]| $d)+ \>
    { tok (eitherResIdent T_MemoryAddress) }

-- Keywords and Ident
$l $i*
    { tok (eitherResIdent TV) }

-- Integer
$d+
    { tok TI }

{
-- | Create a token with position.
tok :: (String -> Tok) -> (Posn -> String -> Token)
tok f p = PT p . f

-- | Token without position.
data Tok
  = TK {-# UNPACK #-} !TokSymbol  -- ^ Reserved word or symbol.
  | TL !String                    -- ^ String literal.
  | TI !String                    -- ^ Integer literal.
  | TV !String                    -- ^ Identifier.
  | TD !String                    -- ^ Float literal.
  | TC !String                    -- ^ Character literal.
  | T_StellaIdent !String
  | T_ExtensionName !String
  | T_MemoryAddress !String
  deriving (Eq, Show, Ord)

-- | Smart constructor for 'Tok' for the sake of backwards compatibility.
pattern TS :: String -> Int -> Tok
pattern TS t i = TK (TokSymbol t i)

-- | Keyword or symbol tokens have a unique ID.
data TokSymbol = TokSymbol
  { tsText :: String
      -- ^ Keyword or symbol text.
  , tsID   :: !Int
      -- ^ Unique ID.
  } deriving (Show)

-- | Keyword/symbol equality is determined by the unique ID.
instance Eq  TokSymbol where (==)    = (==)    `on` tsID

-- | Keyword/symbol ordering is determined by the unique ID.
instance Ord TokSymbol where compare = compare `on` tsID

-- | Token with position.
data Token
  = PT  Posn Tok
  | Err Posn
  deriving (Eq, Show, Ord)

-- | Pretty print a position.
printPosn :: Posn -> String
printPosn (Pn _ l c) = "line " ++ show l ++ ", column " ++ show c

-- | Pretty print the position of the first token in the list.
tokenPos :: [Token] -> String
tokenPos (t:_) = printPosn (tokenPosn t)
tokenPos []    = "end of file"

-- | Get the position of a token.
tokenPosn :: Token -> Posn
tokenPosn (PT p _) = p
tokenPosn (Err p)  = p

-- | Get line and column of a token.
tokenLineCol :: Token -> (Int, Int)
tokenLineCol = posLineCol . tokenPosn

-- | Get line and column of a position.
posLineCol :: Posn -> (Int, Int)
posLineCol (Pn _ l c) = (l,c)

-- | Convert a token into "position token" form.
mkPosToken :: Token -> ((Int, Int), String)
mkPosToken t = (tokenLineCol t, tokenText t)

-- | Convert a token to its text.
tokenText :: Token -> String
tokenText t = case t of
  PT _ (TS s _) -> s
  PT _ (TL s)   -> show s
  PT _ (TI s)   -> s
  PT _ (TV s)   -> s
  PT _ (TD s)   -> s
  PT _ (TC s)   -> s
  Err _         -> "#error"
  PT _ (T_StellaIdent s) -> s
  PT _ (T_ExtensionName s) -> s
  PT _ (T_MemoryAddress s) -> s

-- | Convert a token to a string.
prToken :: Token -> String
prToken t = tokenText t

-- | Finite map from text to token organized as binary search tree.
data BTree
  = N -- ^ Nil (leaf).
  | B String Tok BTree BTree
      -- ^ Binary node.
  deriving (Show)

-- | Convert potential keyword into token or use fallback conversion.
eitherResIdent :: (String -> Tok) -> String -> Tok
eitherResIdent tv s = treeFind resWords
  where
  treeFind N = tv s
  treeFind (B a t left right) =
    case compare s a of
      LT -> treeFind left
      GT -> treeFind right
      EQ -> t

-- | The keywords and symbols of the language organized as binary search tree.
resWords :: BTree
resWords =
  b "cons" 41
    (b ">" 21
       (b "/" 11
          (b "+" 6
             (b "(" 3 (b "&" 2 (b "!=" 1 N N) N) (b "*" 5 (b ")" 4 N N) N))
             (b "->" 9 (b "-" 8 (b "," 7 N N) N) (b "." 10 N N)))
          (b "<=" 16
             (b ";" 14 (b ":=" 13 (b ":" 12 N N) N) (b "<" 15 N N))
             (b "==" 19 (b "=" 18 (b "<|" 17 N N) N) (b "=>" 20 N N))))
       (b "Nat::rec" 31
          (b "List::isempty" 26
             (b "Bot" 24
                (b "Bool" 23 (b ">=" 22 N N) N) (b "List::head" 25 N N))
             (b "Nat::iszero" 29
                (b "Nat" 28 (b "List::tail" 27 N N) N) (b "Nat::pred" 30 N N)))
          (b "and" 36
             (b "[" 34 (b "Unit" 33 (b "Top" 32 N N) N) (b "]" 35 N N))
             (b "cast" 39 (b "auto" 38 (b "as" 37 N N) N) (b "catch" 40 N N)))))
    (b "not" 62
       (b "if" 52
          (b "fix" 47
             (b "exception" 44
                (b "else" 43 (b "core" 42 N N) N)
                (b "false" 46 (b "extend" 45 N N) N))
             (b "forall" 50
                (b "fold" 49 (b "fn" 48 N N) N) (b "generic" 51 N N)))
          (b "language" 57
             (b "inline" 55 (b "inl" 54 (b "in" 53 N N) N) (b "inr" 56 N N))
             (b "match" 60
                (b "letrec" 59 (b "let" 58 N N) N) (b "new" 61 N N))))
       (b "type" 72
          (b "then" 67
             (b "return" 65 (b "panic!" 64 (b "or" 63 N N) N) (b "succ" 66 N N))
             (b "true" 70
                (b "throws" 69 (b "throw" 68 N N) N) (b "try" 71 N N)))
          (b "{" 77
             (b "variant" 75
                (b "unit" 74 (b "unfold" 73 N N) N) (b "with" 76 N N))
             (b "}" 80 (b "|>" 79 (b "|" 78 N N) N) (b "\181" 81 N N)))))
  where
  b s n = B bs (TS bs n)
    where
    bs = s

-- | Unquote string literal.
unescapeInitTail :: String -> String
unescapeInitTail = id . unesc . tail . id
  where
  unesc s = case s of
    '\\':c:cs | elem c ['\"', '\\', '\''] -> c : unesc cs
    '\\':'n':cs  -> '\n' : unesc cs
    '\\':'t':cs  -> '\t' : unesc cs
    '\\':'r':cs  -> '\r' : unesc cs
    '\\':'f':cs  -> '\f' : unesc cs
    '"':[]       -> []
    c:cs         -> c : unesc cs
    _            -> []

-------------------------------------------------------------------
-- Alex wrapper code.
-- A modified "posn" wrapper.
-------------------------------------------------------------------

data Posn = Pn !Int !Int !Int
  deriving (Eq, Show, Ord)

alexStartPos :: Posn
alexStartPos = Pn 0 1 1

alexMove :: Posn -> Char -> Posn
alexMove (Pn a l c) '\t' = Pn (a+1)  l     (((c+7) `div` 8)*8+1)
alexMove (Pn a l c) '\n' = Pn (a+1) (l+1)   1
alexMove (Pn a l c) _    = Pn (a+1)  l     (c+1)

type Byte = Word8

type AlexInput = (Posn,     -- current position,
                  Char,     -- previous char
                  [Byte],   -- pending bytes on the current char
                  String)   -- current input string

tokens :: String -> [Token]
tokens str = go (alexStartPos, '\n', [], str)
    where
      go :: AlexInput -> [Token]
      go inp@(pos, _, _, str) =
               case alexScan inp 0 of
                AlexEOF                   -> []
                AlexError (pos, _, _, _)  -> [Err pos]
                AlexSkip  inp' len        -> go inp'
                AlexToken inp' len act    -> act pos (take len str) : (go inp')

alexGetByte :: AlexInput -> Maybe (Byte,AlexInput)
alexGetByte (p, c, (b:bs), s) = Just (b, (p, c, bs, s))
alexGetByte (p, _, [], s) =
  case s of
    []  -> Nothing
    (c:s) ->
             let p'     = alexMove p c
                 (b:bs) = utf8Encode c
              in p' `seq` Just (b, (p', c, bs, s))

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (p, c, bs, s) = c

-- | Encode a Haskell String to a list of Word8 values, in UTF8 format.
utf8Encode :: Char -> [Word8]
utf8Encode = map fromIntegral . go . ord
  where
  go oc
   | oc <= 0x7f       = [oc]

   | oc <= 0x7ff      = [ 0xc0 + (oc `Data.Bits.shiftR` 6)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]

   | oc <= 0xffff     = [ 0xe0 + (oc `Data.Bits.shiftR` 12)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
   | otherwise        = [ 0xf0 + (oc `Data.Bits.shiftR` 18)
                        , 0x80 + ((oc `Data.Bits.shiftR` 12) Data.Bits..&. 0x3f)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
}
