\documentclass[preprint, 9pt]{sigplanconf}

%include polycode.fmt

\usepackage{fancyvrb}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{url}
\usepackage{pgf}
\usepackage{pdfpages}
\usepackage{booktabs}
\usepackage[numbers]{natbib}  % For URLs in bibliography
\usepackage{subfigure}
\usepackage{color}
\usepackage{mathpartir}
% \usepackage{caption}
% \usepackage{subcaption}

\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}
% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

% General formatting directives/macros
%format subst (term) (v) (e) = [v "\mapsto" e] term
%format ^ = "\mathbin{\char`\^}"
%format a1 = "a_1"
%format a2 = "a_2"
%format c1 = "c_1"
%format c2 = "c_2"
%format e1 = "e_1"
%format e2 = "e_2"
%format a'1 = "a^{\prime}_1"
%format a'2 = "a^{\prime}_2"
%format e'1 = "e^{\prime}_1"
%format e'2 = "e^{\prime}_2"
%format forall (x) = "\mathopen{}\forall" x "\mathclose{}"
%format box = "\Box"
%format triangle = "\triangle"
%format (many (x)) = "\overline{" x "}"
\def\commentbegin{\quad$[\![\enskip$}
\def\commentend{$\enskip]\!]$}

\def\myruleform#1{
\setlength{\fboxrule}{0.5pt}\fbox{\normalsize $#1$}
}
\newcommand{\myirule}[2]{{\renewcommand{\arraystretch}{1.2}\begin{array}{c} #1
                      \\ \hline #2 \end{array}}}

% For typesetting infer rules, found in proof.sty in this directory
\usepackage{proof}
\usepackage{bussproofs}


% If we want white lines in a table
\newcommand{\whiteline}{\\[0.2in]}

\newcommand{\tom}[1]{\textcolor{red}{\textbf{[\textsc{Tom:} \textcolor{black}{#1}]}}}

% Document metadata

\conferenceinfo{WXYZ '05}{date, City.}
\copyrightyear{2005}
\copyrightdata{[to be supplied]}

% \titlebanner{banner above paper title}        % These are ignored unless
% \preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Bringing Functions into the Fold}
% \subtitle{Subtitle Text, if any}

\authorinfo{Jasper Van der Jeugt \and Steven Keuchel \and Tom Schrijvers}{Ghent University, Belgium}{\{jasper.vanderjeugt,steven.keuchel,tom.schrijvers\}@@ugent.be}

\begin{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types      #-}
import Data.Char     (toUpper)
import Prelude       hiding (head, foldr, map, sum, replicate)
\end{code}
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
\tom{To revise:}
Rewriting explicitly recursive functions in terms of higher-order functions such
as |fold| and |map| brings many advantages such as conciseness, improved
readability, and it facilitates some optimisations. However, it is not always
straightforward for a programmer to write functions in this style. We present an
approach to automatically detect these higher-order functions, so the programmer
can have his cake and eat it, too.
\end{abstract}

% TODO: Explicit results, evaluation

\category{CR-number}{subcategory}{third-level}

\terms
term1, term2

\keywords
catamorphisms, fold-build fusion, analysis, transformation 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

Higher-order functions are immensely popular in Haskell, whose Prelude alone
offers a wide range of them (e.g., |map|, |filter|, |any|, \ldots). This is not
surprising, because they the key \emph{abstraction} mechanism of functional
programming languages. They enable capturing and reusing common frequent
patterns in function definitions. 

\emph{Recursion schemes} are a particularly important class of patterns
captured by higher-order functions. They capture forms of recursion found in
explicitly recursive functions and encapsulate them in reusable abstractions.
In Haskell, the |foldr| function is probably the best known example of a recursion
scheme. It captures structural recursion over a list.
\begin{spec}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []      = z
foldr f z (x:xs)  = f x (foldr f z xs)
\end{spec}
By means of a recursion scheme like |foldr|, the programmer can avoid the use
of explicit recrusion in his functions, like
\begin{spec}
sum :: [Int] -> Int
sum []      = 0
sum (x:xs)  = x + sum xs
\end{spec}
in favor of implicit recursion in terms of the recursion scheme:
\begin{spec}
sum :: [Int] -> Int
sum xs = foldr (+) 0 xs
\end{spec}

Gibbons~\cite{gibbons2003} has likened the transition from the former style to the
latter with the transition from imperative programming with \texttt{goto}s to
structured programming. Indeed the use of recursion schemes has many of the
same benefits for program construction and program understanding.

One benefit that has received a lot of attention in the Haskell community is
program optimization. Various equational laws have been devised to \emph{fuse}
the composition of two recursion schemes into a single recursive function.
Perhaps the best-known of these is \emph{shortcut fusion}, also known as
foldr/build fusion~\cite{gill1993}.
%{
%format . = "."
\begin{spec}
  forall c n g. foldr c n (build g) = g c n
\end{spec}
%}
This law fuses a list producer, expressed in terms of |build|, with a list
consumer, experessed in terms of |foldr| in order to avoid the construction
of the allocation of the intermediate list; the latter is called
\emph{deforestation}~\cite{wadler1990}.

A significant weakness of foldr/build fusion and other fusion approaches is
that programmers have to explicitly write their programs in terms of the
appropriate recursion schemes. This is an easy requirement when programmers
only reuse library functions written in the appropriate stlye.  However, when
it comes to writing their own functions, programmers usually resort to explicit
recursion. This not just true of novices, but applies just as well to
experienced Haskell programmers, including, as we will show, the authors of
some of the most popular Haskell packages.

Hence, already in their '93 work on fold/build fusion, Gill et
al.~\cite{gill1993} have put forward an important challenge for the compiler:
to automatically detect recursion schemes in explicitly recursive functions.
This allows programmers to have their cake and eat it too: they can write
functions in their preferred style and still benefit from fusion.

% The latter style emphasizes the non-recursive parts of the 
% 
% The latter style is often more concise, which recent studies~\cite{} have shown
% to be an important factor in program understanding. 
% 
% Probably the best-known example of recursion schemes are folds, and the |foldr|
% function in particular.
% 
%  A particularly important use of higher-order
% functions is to express \emph{recursion schemes}.
% 
%  among,
% often recursive, function definitions to a much larger extent than first-order
% functions. In addition to the obvious code reuse and increased programmer
% productivity, uses of higher-order functions have many other potential
% advantages over conventional first-order definitions.
% \begin{itemize}
% \item Uses of higher-order functions can be more quickly understood because
%       they reduce the that is already known pattern to a single name and thus draw
%       the attention immediately to what is new (i.e., the function parameters).
% 
% \item Because the code is more compact and the number of bugs is proportional
%       to code size~\cite{gaffney1984}, higher-order functions should lead to
%       fewer bugs.
% 
% \item Properties can be established for the higher-order function indepently
%       from its particular uses. This makes (e.g., equational) reasoning more productive.
% 
% \item Since properties and occurrences are more readily available, they make good targets
%       for automatic optimization in compilers.
% \end{itemize}
% 
% A particularly ubiquitous pattern is that of folds or \emph{catamorphisms}. In
% the case of lists, this pattern has been captured in the well-known |foldr|
% function.
% \begin{code}
% foldr :: (a -> b -> b) -> b -> [a] -> b
% foldr _ z []        = z
% foldr f z (x : xs)  = f x (foldr f z xs)
% \end{code}
% Indeed, the research literature is full of applications,
% properties and optimizations based on folds. \tom{add many citations}
% 
% Hence, given all these advantages of folds, one would expect every programmer
% to diligently avoid explicit recursion where folds can do the job.
% Unfortunately, that is far from true in practice. For many reasons, programmers
% do not write their code in terms of explicit folds. This class comprises a
% large set of advanced functional programmers \tom{evidence of our case study}.
% This is compounded by the fact that programmers often do not bother to define
% the equivalent of |foldr| for other inductive algebraic datatypes.
% 
% Yet, sadly, these first-order recursive functions are treated as second-class
% by compilers. They do not benefit from the same performance gains like loop
% fusion and deforestations. In fact, the leading Haskell compiler GHC won't even
% inline recursive functions. We disagree with this injustice and argue that it
% is quite unnecessary to penalize programmers for using first-class recursion.
% In fact, we show that with a little effort, catamorphisms can be detected
% automatically by the compiler and automatically transformed into explicit
% invocations of folds for the purpose of automation.

As far as we know, this work is the first to pick up that challenge and automatically
detect recursion schemes in a Haskell compiler.
Our contributions are in particular:
\begin{enumerate}
\item We show how to automatically identify and transform explicitly recursive functions 
      that can be expressed as folds. 
\item In order to support a particular well-known optimization,
      fold-build fusion, we also show how to automatically detect and transform
      functions that can be expressed as a call to |build|.
\item We provide a GHC compiler plugin that performs these detections and
      transformations on GHC Core. Our plugin not
      only covers folds and builds over lists, but over all inductively defined
      directly-recursive datatypes. 

\item A case study shows that our plugin is effective on a range of
      well-known Haskell packages. It identifies a substantial number of
      explicitly recursive functions that fit either the fold or build pattern, 
      reveals that our approach works well with GHC's existing list fusion 
      infrastructure.
\end{enumerate}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newpage
\section{Overview}

% In the early days of computing, assembly code was used for writing programs. In
% assembly, the control flow of a program is controlled using \emph{jumps}. This
% convention was continued in early programming languages, and developers
% manipulated the control flow of their applications using the \texttt{goto}
% construct. This allowed \emph{arbitrary} jumps through code, which brought with
% it many disadvantages \cite{dijkstra1968}. In particular, it could be very hard
% to understand code written in this style.
% 
% Later programming languages favoured use of control stuctures such as
% \texttt{for} and \texttt{while} over \texttt{goto}. This made it easier for
% programmers and tools to reason about these structures.
% 
% For example, loop invariants can be used to reason about \texttt{while} loops:
% 
% \begin{center}
% \mbox{
%     \infer{
%         \left\{ I \right\} \text{while} (C) ~ \text{body}
%         \left\{ \lnot C \wedge I \right\}
%     }{
%         \left\{C \wedge I\right\} \text{body} \left\{ I \right\}
%     }
% }
% \end{center}
% 
% Additionally, \texttt{goto}-based code can be much harder to understand: the
% developer needs to understand the function in its entirety before arriving at a
% basic understanding of the control flow.
% 
% A similar argument can be made about \emph{explicit recursion} in functional
% programming languages. Consider the simple functions:

%-------------------------------------------------------------------------------
\subsection{Folds}

\emph{Catamorphisms} are functions that \emph{consume} an inductively defined datastructure
by means of structural recursion.  Here are two examples of catamorphisms over
the most ubiquitous inductive datatype, lists.
\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs

product :: [Int] -> Int
product []        = 1
product (x : xs)  = x * product xs
\end{code}

Instead of using explicit recursion again and again, the catamorphic 
pattern can be captured once and for all in a higher-order
function, the fold function. In case of list, that fold function is |foldr|.
\begin{code}
upper = foldr (\x xs -> toUpper x : xs) []

product = foldr (*) 1
\end{code}

% - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Folds with Parameters}
Some catamorphisms take extra parameters to compute their result. Hinze et al.~\cite{urs}
distinguish two kinds of extra parameters: \emph{constant} and \emph{accumulating} parameters.
List concatenation is an example of the former:
\begin{spec}
cat :: [a] -> [a] -> [a]
cat []      ys  = ys
cat (x:xs)  ys  = x : cat xs ys
\end{spec}
The |ys| parameter is a constant parameter because it does not change in the
recursive calls. We can get rid of this constant parameter by hoisting it out of
the loop. 
\begin{spec}
cat :: [a] -> [a] -> [a]
cat l ys = loop l
  where
    loop :: [a] -> [a]
    loop []      = ys
    loop (x:xs)  = x : loop xs
\end{spec}
Now, the local function can be rewritten in terms of a |foldr| without having
to bother with passing the constant parameter.
\begin{spec}
cat xs ys  = loop l
  where
    loop l = foldr (:) ys l
\end{spec}
Finally, we can inline the local function entirely.
\begin{spec}
cat xs ys  = foldr (:) ys l
\end{spec}
To cut a long story short, we can directly rewrite functions with constant
parameters in terms of |foldr| without taking special precautions for constant
parameters.

Accumulating parameters are trickier to deal with as they may vary in
recursive calls. An example is the accumulator-based sum function:
\begin{code}
sumAcc :: [Int] -> Int -> Int
sumAcc []      acc  = acc
sumAcc (x:xs)  acc  = sumAcc xs (x + acc)
\end{code}
where the |acc| parameter varies in the recursive call.
Typically, such a function is defined in terms of the |foldl| variant of |foldr|,
which folds from the left rather than the right.
\begin{code}
foldl :: (a -> b -> a) -> a -> [b] -> a
foldl f z []      = z
foldl f z (x:xs)  = foldl f (f z x) xs

sumAcc l acc  = foldl (+) acc l
\end{code}
However, these functions too can be expressed in terms of |foldr|.
The trick is to see such a function not as \emph{having} an extra parameter
but as \emph{returning} a function that takes a parameter. For instance,
|sumAcc| should not be considered as a function that takes a list and an integer
to an integer, but a function that takes a list to a function
that takes an integer to an integer. This becomes more apparent when we make
the precedence of the function arrow in the type signature explicit, as well as
the binders for the extra parameter.
\begin{code}
sumAcc :: [Int] -> (Int -> Int)
sumAcc []      = \acc -> acc
sumAcc (x:xs)  = \acc -> sumAcc xs (x + acc)
\end{code}
Now we have an obvious catamorphism without extra parameter
that can be turned trivially into a fold.
\begin{code}
sumAcc l = foldr  (\x xs acc -> xs (x+acc)) 
                  (\acc -> acc) l
\end{code}
As a last step we may want to $\eta$-expand the above definition.
\begin{code}
sumAcc l acc = foldr  (\x xs acc -> xs (x+acc)) 
                      (\acc -> acc) l acc
\end{code}

Finally, |foldl| is an example of a function with both
a constant parameter |f| and an accumulating parameter
|z|. It is expressed as a |foldr| thus:
\begin{code}
foldl f z l  = foldr (\x xs z -> xs (f x z)) (\z -> z) l z
\end{code}
Note that as a minor complication both extra parameters precede
the list parameter.

% - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Other Datatypes}

While we have shown the above example on lists, the above ideas easily
generalize to other inductively defined algebraic datatypes.
We illustrate that on leaf trees.
\begin{code}
data Tree a
    = Leaf a
    | Branch (Tree a) (Tree a)
\end{code}

The |sumTree| function is an example of a directly recursive catamorphism
over leaf trees.
\begin{code}
sumTree :: Tree Int -> Int
sumTree (Leaf x)      = x
sumTree (Branch l r)  = sumTree l + sumTree r
\end{code}
This catamorphic recursion scheme can be captured in a fold function too.
The generic idea is that a fold functions transforms the inductive datatype
into a value of a user-specified type |r| by replacing every construtor
with a user-specified function.
\begin{code}
foldT     ::  (a -> r)
          ->  (r -> r -> r)
          ->  Tree a
          ->  r
foldT l _ (Leaf x)      = l x
foldT l b (Branch x y)  =
    b (foldT l b x) (foldT l b y)
\end{code}

The fold over leaf trees enables us to define |sumTree'| succinctly as
\begin{code}
sumTree = foldT id (+)
\end{code}
Leaf trees also have a counterpart of left folds for lists, where the pattern
is called \emph{downward accumulation}. For instance, the following function
from~\cite{urs} labels every leaf with its depth:
\begin{spec}
depths :: Tree a -> Int -> Tree Int
depths (Leaf x)      d  = Leaf d
depths (Branch l r)  d  = Branch  (depths l (d+1)) 
                                 (depths r (d+1))
\end{spec}
This catamorphism is rewritten into a fold in a similar way as left folds.
\begin{spec}
depths t d  = 
  foldT  (\d -> Leaf d) 
         (\l r d -> Branch (l (d+1)) (r (d+1))) t d
\end{spec}


%-------------------------------------------------------------------------------
\subsection{Builds}

Builds are the opposite of folds: they \emph{produce} datastructures.
For lists, this production pattern is captured in the function |build|.
%{
%format . = "."
\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}
%}
where |g| is a function that builds an abstract list in terms of the provided
`cons' and `nil' functions. The |build| function constructs a concrete list
by applying |g| to the conventional |(:)| and |[]| list constructors.

Consider for instance the function |replicate|.
\begin{code}
replicate :: Int -> a -> [a]
replicate n x
    | n <= 0     = []
    | otherwise  = x : replicate (n - 1) x
\end{code}
which can be expressed in terms of |build| as follows:
\begin{code}
replicate n x = build (\cons nil ->
  let g n x 
        | n <= 0    = nil
        | otherwise  = cons x (g (n - 1) x)
  in g n x)
\end{code}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Other Datatypes}
The notion of a build function also generalizes. For instance,
this is the build function for leaf trees:
%{
%format . = "."
\begin{code}
buildTree  ::  (forall b. (a -> b) -> (b -> b -> b) -> b)
           ->  Tree a
buildTree g = g Leaf Branch
\end{code}
%}

With this build function we can express a producer of leaf trees
\begin{code}
range :: Int -> Int -> Tree a
range l u
  | u > l      =  let m = l + (u - l) `div` 2
                  in  Branch (range l m) (range (m+1) u)
  | otherwise  =  Leaf l
\end{code}
as a build:
\begin{code}
range l u  = 
  buildTree (\leaf branch -> 
    let g l u
          | u > l      =  let m = l + (u - l) `div` 2
                          in  branch (g l m) (g (m+1) u)
          | otherwise  =  leaf l
    in g l u)
\end{code}

%-------------------------------------------------------------------------------
\subsection{Fold/Build Fusion}

The foldr/build fusion rule expresses that a consumer and producer can be fused:
\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]

Consider the following expressions:
\begin{spec}
sum (replicate n x)
\end{spec}
which consumes a list with |sum| after generating it with |replicate|.  With
the help of the fusion rule and simple transformations, we can optimize it as
follows.
\begin{spec}
    sum (replicate n x)

== {- inline |sum| -}

    foldr (+) 0 (replicate n x)

== {- inline |replicate| -}

    foldr (+) 0 (build $ \cons nil ->
        let g n x
                | n <= 0     = nil
                | otherwise  = cons x (g (n - 1) x)
        in g n x)

== {- foldr/build fusion -}

    (\cons nil ->
        let g n x
                | n <= 0     = nil
                | otherwise  = cons x (g (n - 1) x)
        in g n x) (+) 0

== {- $\beta$-reduction -}

    let g n x
            | n <= 0     = 0
            | otherwise  = x + g (n - 1) x
    in g n x

\end{spec}
Although arguable less readable, we can see that the final version of |sum
(replicate n x)| does not create an intermediate list.

\paragraph{Pipelines}
Haskell best practices encourage building complicated functions by producing,
repeatedly transforming and finally consuming an intermediate datastructure in a pipeline. An
example of such a pipeline is the following sum-of-odd-squares function:
\begin{code}
sumOfSquaredOdds' :: Int -> Int
sumOfSquaredOdds' = 
  sum . map (^ 2) . filter odd . enumFromTo 1
\end{code}
This code is quite compact and easy to compose from existing library functions.
However, when compiled naively, it is also rather inefficient because it
performs three loops and allocates two intermediate lists ( one as a result of
|filter odd|, and another as result of |map (^ 2)|) that are immediately
consumed again.

With the help of |fold|/|build| fusion, whole pipelines like |sumOfSquareOdds| can be
fused into one recursive function:
\begin{code}
sumOfSquaredOdds :: Int -> Int
sumOfSquaredOdds n = go 1
  where
   go :: Int -> Int
   go x
     | x > n      = 0
     | odd x      = x ^ 2 + go (x+1)
     | otherwise  = go (x+1)
\end{code}
which performs only a single loop and allocates no intermediate lists. 

The key to pipeline optimization is the fact that \emph{transformation functions}
like |map| and |filter| can be expressed as a |build| whose generator
function is a |fold|.
\begin{spec}
map :: (a -> b) -> [a] -> [b]
map f l = build (\cons nil -> foldr (cons . f) nil l)

filter :: (a -> Bool) -> [a] -> [a]
filter p l = 
  build (\cons nil -> foldr (\x -> if p x  then cons x 
                                           else id) nil l)
\end{spec}
This means they can fuse with both a consumer on the left and a producer on the
right.

\paragraph{Other Datatypes}
Any datatype that provides both a fold and build function, has a corresponding
fusion law. For leaf trees, this law is:
\[ |foldT leaf branch (buildTree g)| ~~ |==| ~~ |g leaf branch| \]

It is key to fusing two loops into one:
\begin{spec}
    sumTree (range l u)

== {- inline |sumTree| -}

    foldT id (+) (range l u)

== {- inline |range| -}

    foldT id (+) (buildTree $ \leaf branch ->
        let g l u
		| u > l      =  let m = l + (u - l) `div` 2
		                in  branch (g l m) (g (m+1) u)
		| otherwise  =  leaf l
        in g l u)

== {- fold/build fusion -}

    (\leaf branch ->
        let g l u
		| u > l      =  let m = l + (u - l) `div` 2
		                in  branch (g l m) (g (m+1) u)
		| otherwise  =  leaf l
        in g l u) id (+)

== {- $\beta$-reduction -}

    let g l u
    	| u > l      =  let m = l + (u - l) `div` 2
    	                in  g l m + g (m+1) u
    	| otherwise  =  l
    in g l u

\end{spec}


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \subsection{foldr/foldr fusion}
% 
% TODO: Give a quick overview what foldr-foldr fusion is. Explain we don't
% implement it, but that our work facilitates the optimisation.

%-------------------------------------------------------------------------------
\subsection{Automation}

The main Haskell compiler, GHC, automates fold/build fusion by means of its
rewrite rules infrastructure~\cite{jones2001}. The fusion law is expressed
as a rewrite rule in the GHC.Base module
\begin{Verbatim}
  {-# RULES
  "fold/build"  
     forall k z (g::forall b. (a->b->b) -> b -> b) .
     foldr k z (build g) = g k z
   #-}
\end{Verbatim}
which is applied whenever the optimizer encounters the pattern on the left. In
addition, various library functions have been written\footnote{or come with
rewrite rules that rewrite them into those forms} in terms of |foldr| and
|build|. Whenver the programmer uses these functions and combines them
with his own uses of |foldr| and |build|, fusion may kick in.

Unfortunately, GHC's infrastructure shows two main weaknesses:
\begin{enumerate}
\item 
  GHC does not explicitly cater or other datatypes than lists.
  While the programmer can replicate the existing list infrastructure for his
  own datatypes, it requires a considerable effort and rarely happens in practice.
\item
  Programmers or libraries need to explicitly define their functions
  in terms of |foldr| and |build|. If they don't, then fusion is not possible.
  This too turns out to be too much to ask as we see many uses of explicit
  recursion in practice (see Section~\ref{}).
\end{enumerate}

This work addresses both limitations. It allows programmers to write their
functions in explicitly recursive style and performs fold/build fusion for any
directly inductive datatype.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Finding Folds}
\label{subsection:identifying-folds}

This section explains our approach to turning explicitly recrusive functions
into invocations of |fold|.

%-------------------------------------------------------------------------------
\subsection{Syntax and Notation}
\label{section:core-expressions}

To simplify the presentation, we do not explain our approach in terms of
Haskell source syntax or even GHC's core syntax (based on System F). Instead,
we use the untyped lambda-calculus extended with constructors and pattern
matching, and (possibly recursive) bindings.  
%{
%format (many (x)) = "\overline{" x "}"
\begin{center}
\begin{tabular}{llcl}
binding     & |b| & ::=  & |x = e|  \\
pattern     & |p| & ::=  & |K (many (x))| \\
expression  & |e| & ::=  & |x| \\
            &     & $\mid$ & |e e| \\
            &     & $\mid$ & |\x -> e| \\
            &     & $\mid$ & |K| \\
            &     & $\mid$ & |case e of many (p -> e)|
\end{tabular}
\end{center}
%}
The extension to GHC's full core syntax, including
types, is relatively straightforward. 

We will also need an advanced form of \emph{(expression) context}:
\[\begin{array}{lcl}
|E| & ::=  & |x| \\
    & \mid & |E x| \\
    & \mid & |E box| \\
    & \mid & |E triangle|
\end{array}\]
A context |E| denotes a function applied to a number of arguments. The function
itself and some of its arguments are given (as variables), while there are holes for the other
arguments. In fact, there are two kinds of holes: boxes |box| and triangles
|triangle|. The former is used for a sequence of extra parameters, while
the latter marks the main argument on which structural recursion is performed. The function
$|E|[|many e|;e]$ turns a context |E| into an expression by filling in the holes
with the given expressions.
\[\begin{array}{lcl}
|x|[\epsilon;|e|]                   & =  & |x| \\
(|E x|)[|many e|;|e|]         & =  & |E|[|many e|;|e|]\, |x| \\
(|E box|)[|many e|,|e1|;|e|]  & =  & |E|[|many e|;|e|]\, |e1| \\
(|E triangle|)[|many e|;|e|]  & =  & |E|[|many e|;|e|]\, |e| \\
\end{array}\]
Note that this function is partial; it is undefined if the number
of expressions |many e| does not match the number of box holes.

%-------------------------------------------------------------------------------
\subsection{Finding Folds}
\label{subsection:identifying-folds}

\begin{figure*}[t]
\begin{center}
\fbox{
\begin{minipage}{0.95\textwidth}
\[\begin{array}{c}
\myruleform{\inferrule{}{b \leadsto b'}} \hspace{2cm}

\inferrule*[left=(\textsc{F-Bind})]
  { |e'1| = [|x| \mapsto |[]|]|e1| \\ |f| \not\in \mathit{fv}(|e'1|) \\\\ 
    |E|[|many u|;|y|] = |f (many x) y (many z)| \\ |ws|~\textit{fresh} \\\\ 
    |e2| \stackrel{E}{\leadsto}_{|ws|}^{|vs|} |e'2| \\ \{ f, x, vs \} \cap \mathit{fv}(|e'2|) = \emptyset
  }
  {
|f = \(many x) y (many z) -> case y of { [] -> e1 ; (v:vs) -> e2 }| \\\\
    \leadsto |f = \(many x) y (many z) -> foldr (\v ws (many u) -> e'2) (\many u -> e'1) y (many u)| 
  } \\
\\
\myruleform{\inferrule*{}{e~{}_x\!\!\stackrel{E}{\leadsto}_y~e'}} \hspace{2cm}
\inferrule*[left=(\textsc{F-Rec})]
  { e_i~{}_x\!\!\stackrel{E}{\leadsto}_y~e_i' \quad (\forall i)
  }
  { |E|[|many e|;|x|] ~{}_x\!\!\stackrel{E}{\leadsto}_y~|y (many e')|
  }
  \hspace{1cm}
\inferrule*[left=(\textsc{F-Refl})]
  { 
  }
  { e~{}_x\!\!\stackrel{E}{\leadsto}_y~e
  }
 \\
\\
\inferrule*[left=(\textsc{F-Abs})]
  { |e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'|
  }
  { |\z -> e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|\z -> e'|
  }
  \hspace{0.5cm}
\inferrule*[left=(\textsc{F-App})]
  { |e1|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'1| \\
    |e2|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'2|
  }
  { |e1 e2|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'1 e'2|
  }
 \\
\\
\inferrule*[left=(\textsc{F-Case})]
  { |e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'| \\ e_i~{}_x\!\!\stackrel{E}{\leadsto}_y~e_i' \quad (\forall i)
  }
  { |case e of many (p -> e)|~{}_x\!\!\stackrel{E}{\leadsto}_y~|case e' of many (p -> e')|
  } \\
\end{array} \]
\end{minipage}
}
\end{center}
\caption{Fold discovery rules}\label{fig:foldspec}
\end{figure*}


Figure~\ref{fig:foldspec} shows our non-deterministic algorithm for rewriting 
function bindings in terms of folds. To keep the exposition simple, the algorithm
is specialized to folds over lists; we discuss the generalization to other
algebraic datatypes later on.

\paragraph{Single-Argument Functions}
The top-level judgement is of the form $|b| \leadsto |b'|$, which denotes the
rewriting of a function binding |b| to |b'|.  The judgement is defined by a
single rule \textsc(F-Bind), but we first explain a specialized rule for single
argument functions:
\[
\inferrule*[left=(\textsc{F-Bind'})]
  { |e'1| = [|x| \mapsto |[]|]|e1| \\ |f| \not\in \mathit{fv}(|e1|) \\ |ws|~\textit{fresh} \\\\ 
    |e2| \stackrel{|f triangle|}{\leadsto}_{|ws|}^{|vs|} |e'2| \\ \{ f, x, vs \} \cap \mathit{fv}(|e'2|) = \emptyset
  }
  {
|f = \y -> case y of { [] -> e1 ; (v:vs) -> e2 }| \\\\
    \leadsto |f = \y -> foldr (\v ws -> e'2) e'1 y| 
  }
\]
This rule rewrites a binding like
\begin{spec}
sum = \y -> case y of
              []      -> 0
              (v:vs)  -> (+) v (sum vs)
\end{spec}
into
\begin{spec}
sum = \y -> foldr (\v ws -> (+) v ws) 0 y
\end{spec}
mostly by simple pattern matching and replacement. The
main work is to replace all recursive calls in |e2|, which
is handled by the auxiliary judgement of the form
\[ e~{}_x\!\!\stackrel{E}{\leadsto}_y~e' \]
which is defined by five rewriting rules: rule \textsc{(F-Rec)} takes care of
the actual rewriting of recursive calls, while rule \textsc{F-Refl} provides
the reflexive closure and the other three rules provide congruence closure.
In the restricted setting of single argument functions rule \textsc({F-Rec}) takes the simplified
form
\[
\inferrule*[left=(\textsc{F-Rec'})]
  { 
  }
  { |f x| ~{}_x\!\!\stackrel{|f triangle|}{\leadsto}_y~ |y|
  }
\]
Hence, we have $|sum vs| ~{}_\mathit{vs}\!\!\!\!\!\!\stackrel{|sum triangle|}{\leadsto}\!\!\!\!\!\!_\mathit{ws}~ |ws|$.

The side-conditions on the \textsc{(F-Bind')} rule make sure that the function being rewritten is
a proper catamorphism.
\begin{enumerate}
\item If |vs| appears in |e'2| as part of $|f vs|$, the latter
      has not been properly replaced by |ws|. If |vs| appears in any other capacity,
      then the function is not a catamorphism, but a \emph{paramorphism}. An example of such a
      function, is the function |suffixes|.
\begin{spec}
suffixes = \y -> case y of
                  []      -> []
                  (v:vs)  -> vs : suffixes vs
\end{spec}
This function can be written as 
\begin{spec}
suffixes = para (\v vs ws -> vs : ws) []
\end{spec}
where the higher-order pattern of paramorphisms is
\begin{spec}
para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para f z []      = z
para f z (x:xs)  = f x xs (para f z xs)
\end{spec}
\item If |f| appears in any other form than as part of recursive calls of the form $|f vs|$, then
      again the function is not a proper catamorphism. An example of that case
      is the following non-terminating function:
\begin{spec}
f = \x -> case x of
            []      -> 0
            (v:vs)  -> v + f vs + f [1,2,3]
\end{spec}
\end{enumerate}
Note that we know in the branches |e1| and |e2| the variable |x| is an alias
for respectively |[]| or |(y:ys)|. Rule (\textsc{F-Bind'}) exploits the former
case to eliminate |x| in |e'1|. The latter case reveals an improper
catamorphism, where |ys| appears outside of a recursive call (issue 2 above);
hence, rule \textsc{(F-Bind')} does not allow it.

\paragraph{Folds with Parameters}
Rule \textsc{(F-Bind)} generalizes rule \textsc{(F-Bind')} by supporting
additional parameters |many x| and |many z| before and after the scrutinee
argument |y|. The algorithm supports both constant and accumulating parameters.
% kinds of additional arguments.
% The first kind are arguments that are \emph{invariant} in the recursion. An
% example of that is the |f| parameter in the |map| function.
% \begin{spec}
% map = \f y -> case y of
%                 []      -> []
%                 (v:vs)  -> (:) (f v) (map f vs)
% \end{spec}
Rule \textsc{(F-Bind)} does not explicitly name the constant parameters, but
captures them instead in the recursive call context |E|. For instance, for |cat|
the context has the form |cat triangle ys|.

% The second kind of additional arguments are \emph{variant} in the recursion.
% Catamorphisms with an accumulating parameter are typical examples of these. E.g.,
% \begin{spec}
% sum' = \y acc -> case y of
%                    []      -> acc
%                    (v:vs)  -> sum' vs (v + acc)
% \end{spec}
Rule \textsc({F-Bind)} names the accumulating parameters |many u| and leaves |box|
holes in the context |E| for them. For instance, the context of |sumAcc| is |sumAcc
triangle box|.  Because the |many u| arguments vary throughout the iteration,
their current and new values need to be bound, respectively supplied, at every
step. The binding of the current values is taken care of by the binders |\many
u ->| in the two first parameters of |foldr|. Also the initial values for |many
u| are supplied as extra parameters to |foldr|.

Rule \textsc{(F-Rec)} captures the new values |many e| for the accumulating
parameters with the help of the context |E|; a recursive call takes the form
$|E|[|many e|;|vs|]$. The rule passes these variant arguments explicitly to the
recursive result |ws|. 
% For instance, after rewriting |sumAcc| we get
% \begin{spec}
% sum' = \y acc -> foldr  (\v ws acc -> ws (v + acc)) 
%                         (\acc -> acc) y acc
% \end{spec}

Note that rule \textsc{(F-Rec)} recursively rewrites the accumulating parameters 
|many e| because they may harbor further recursive calls. For instance,
\begin{spec}
f = \y acc -> case y of
               []      -> acc
               (v:vs)  -> f vs (f vs (v+acc))
\end{spec}
is rewritten to
\begin{spec}
f = \y acc -> foldr (\v ws acc -> ws (ws (v+acc)))
                    (\acc -> acc) y acc
\end{spec}

%-------------------------------------------------------------------------------
\subsection{Degenerate folds}
\label{subsection:degenerate-folds}

Our algorithm also transforms certain non-recursive
functions into folds. For instance, it rewrites
\begin{code}
head :: [a] -> a
head = \l -> case l of
               []      ->  error "empty list"
               (x:xs)  ->  x
\end{code}
into
\begin{code}
head :: [a] -> a
head = \l -> foldr (\z zs -> z) (error "empty list") l
\end{code}
These \emph{degenerate} folds are of no interest to us, since non-recursive functions
are much more easily understood in their conventional form than as a fold. Moreover, they can
easily be optimized without 
fold/build fusion: by simple inlining and specialization. 
Fortunately we can easily avoid introducing degenerate folds by only rewriting
recursive functions. In other words, the algorithm must use 
the rule \textsc{(F-Rec)} at least once.

%-------------------------------------------------------------------------------
\subsection{Other Datatypes}

The algorithm generalizes straightforwardly to other datatypes than lists.  The
main issues are to cater for the datatype's constructors rather than those of
lists, and to use the datatype's fold function rather than |foldr|.

A significant generalization from lists is that datatype constructors may have
multiple recursive subterms. For instance, the |Branch| constructor of our
leaf trees has two recursive subterms, for the left and right subtrees. This
means that the \textsc(F-Rec) rule has to allow for recursive calls over
either. Also note that in the case of multiple recursive subterms, the
recursive rewriting of accumulating parameters in rule \textsc{F-Rec} is more
likely to occur. Consider for instance the following function
\begin{spec}
flatten :: Tree a -> [a] -> [a]
flatten = \t acc -> case t of
                      Leaf x      -> (x:acc)
                      Branch l r  -> flatten l (flatten r acc)
\end{spec}
which is turned into
\begin{spec}
flatten = \t acc -> foldT  (\x acc -> (x:acc))
                           (\l r acc -> l (r acc)) t acc
\end{spec}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Finding Builds}

\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.95\columnwidth}
\[\begin{array}{c}
\myruleform{\inferrule*{}{|b| \rightarrowtail |b'|;|b''|}} \quad\quad
\inferrule*[left=(\textsc{B-Bind})]
        { |c|, |n|, |g|~\text{fresh}\\\\
          e ~{}_f\!\stackrel{c,n}{\rightarrowtail}_g~ e' }
        {|f = \many x -> e| ~~\rightarrowtail \\\\ 
          |f = \many x -> build (g (many x))|; \\\\
          |g = \many x -> \c -> \n -> e'|
             } \\
\\
\myruleform{\inferrule*{}{|e| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |e'|}} 
\quad\quad
\inferrule*[left=(\textsc{B-Rec})]
        {  }
        { |f (many e)| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |g (many e) c n| }  \\
\\
\inferrule*[left=(\textsc{B-Nil})]
        {  }
        { |[]| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |n| }  
\quad\quad
\inferrule*[left=(\textsc{B-Cons})]
        { |e2| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |e'2| }
        { |(e1:e2)| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |c e1 e'2| }  \\
\\
\inferrule*[left=(\textsc{B-Build})]
        {  }
        { |build e| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |e c n| }  \\
\\
%format e_i = "e'_i"
%format ei = "\Varid{e}_i"
\inferrule*[left=(\textsc{B-Case})]
        { e_i ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ e_i'\quad (\forall i) }
        { |case e of many (p -> e)| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |case e of many (p -> e')| }  \\
\end{array}\]
\end{minipage}
}
\end{center}
\caption{Build discovery rules}\label{fig:buildspec}
\end{figure}

Figure~\ref{fig:buildspec} lists our non-deterministic algorithm for
finding list builds. The toplevel judgement is $b \rightarrowtail b';
b_g$.  It rewrites a binding |b| into |b'| that uses |build| and also returns
an auxiliary binding $b_g$ for the generator function used in the |build|.
There is one rule defining this judgement, (\textsc{B-Bind}), that rewrites
the body |e| of a binding into a |build| and produces the generator function binding.
Note that the rule allows for an arbitrary number of lambda abstractions |\many
x ->| to precede the invocation of |build|. This allows auxiliary parameters to
the generator function, e.g., to support an inductive definition. For instance, the
|map| function can be written as a |build| with two auxiliary parameters.
\begin{spec}
map = \f -> \l -> build (g f l)

g   = \f -> \l -> \c -> \n -> 
        case l of
          []      -> n
          (y:ys)  -> c (f y) (g f ys c n)
\end{spec}
Only the |f| parameter is constant. The |l| parameter changes in inductive calls as |g| is defined inductively over it.

The toplevel judgement is defined in terms of the auxiliary judgement \[|e| ~{}_{|f|}\!\stackrel{|c|,|n|}{\rightarrowtail}_{|g|}~ |e'|\]
that yields the body of the generator function.
This judgement is defined by five different rules, the last of which, (\textsc{B-Case}), is merely
a congruence rule that performs the rewriting in the branches of a |case| expression.
The first four rules distinguish four ways in which the function body can yield a list.
\begin{enumerate}
\item Rule (\textsc{B-Nil}) captures the simplest way for producing a list, namely with |[]|,
      which is rewritten to the new parameter |n|.
\item Rule (\textsc{B-Cons}) replaces the |(:)| constructor with the new parameter |c|, and recursively
      rewrites the tail of the list.
\item Rule (\textsc{B-Rec}) replaces recursive calls to the original function |f| by recursive
      calls to the generator function |g|.
\item Rule (\textsc{B-Build}) deals with the case where a list is produced by a call
      to |build|. In this situation the abstract |c| and |n| list constructors
      can be introduced dynamically as |foldr c n (build e)|. However, this
      expression can of course be statically fused to |e c n|.
\end{enumerate}
In the |map| example, all rules but (\textsc{B-Build}) are used.
Here is an example that does use rule (\textsc{B-Build}).
\begin{spec}
toFront :: Eq a => a -> [a] -> [a]
toFront x xs = x : filter (/= x) xs
\end{spec}
After inlining |filter|, which itself is expressed as a build, this function becomes.
\begin{spec}
toFront = \x -> \xs -> x : build (g (/= x) xs)
\end{spec}
which can be transformed into:
\begin{spec}
toFront = \x -> \xs -> build (g' x xs)
g'  = \x -> \xs -> \c -> \n ->  c x (g' (/= x) xs c n)
\end{spec}
%-------------------------------------------------------------------------------
\paragraph{Degenerate Builds}

Just like non-recursive catamorphisms we can also call non-recursive builds
degenerate.
For instance,
\begin{spec}
f = 1 : 2 : 3 : []
\end{spec}
is rewritten to
\begin{spec}
f  = build g
g  = \c -> \n -> c 1 (c 2 (c 3 n))
\end{spec}
These functions can be easily identified by the absence of a recursive call. 
In other words, the rule (\textsc{B-Rec}) is never used in the rewriting process.

Strictly speaking, such non-recursive functions do not require |fold|/|build|
fusion to be optimized. They can also be optimized by inlining their 
definition and then unfolding the catamorphism sufficiently to consume the
whole list.
\begin{spec}
     sum f
== {- inline |f| -}
     sum (1 : 2 : 3 : [])
== {- unfold |sum| -}
     1 + sum (2 : 3 : [])
== {- unfold |sum| three more times -}
     1 + (2 + (3 + 0))
\end{spec}
However, in practice, GHC does not peform such aggressive inlining by default.
Hence, |fold|/|build| fusion is still a good way of getting rid of the
intermediate datastructure.

%-------------------------------------------------------------------------------
\paragraph{Other Datatypes}

The adaptation of the build algorithm to other datatypes is essentially similar to
the adaptations we had to make for the fold algorithm: cater for a different set 
of constructors with other recursive positions and use the datatype's build function.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}

In fact, the fold function for an inductive
datatype can be derived automatically from its definition. We have implemented
a Template Haskell~\cite{sheard2002} routine, |deriveFold|, to do so. For example, 
%{
%format Tree = "`Tree"
\begin{spec}
$(deriveFold Tree "foldT")
\end{spec}
%}

generates the fold function, named |foldT|, for the type |Tree|.

Just like for folds, we have automated the writing
of build functions with Template Haskell:

%{
%format Tree = "`Tree"
\begin{spec}
$(deriveBuild Tree "buildTree")
\end{spec}
%}
yields the build function, named |buildTree|, for the type |Tree|.

\begin{itemize}
\item mutually recursive functions
\item types
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The GHC Core language}
\label{subsection:ghc-core}

We already gave a brief, high-level explanation of the Core language in section
\ref{section:core-expressions}. In the next few sections, we explain how we
obtain and manipulate this language in practice.

GHC \cite{ghc} is the de-facto compiler for Haskell, altough some alternatives
exist. We selected GHC as target for our implementation because of this reason.

By choosing GHC, we have two convenient representations of Haskell code at our
disposal for analsis.

The most straightforward representation is the Haskell source code itself.
There are numerous parsing libraries to make this task easier
\cite{haskell-src-exts}.

However, during compilation, the Haskell code is transformed to the GHC Core
\cite{tolmach2009} language in a number of passes.

The latter is particulary interesting for our purposes. It offers the following
advantages over regular Haskell source code:

\begin{itemize}

\item First, GHC Core is a much less complicated language than Haskell, because
all syntactic features have been stripped away. As an illustration, the |Expr|
type used by \emph{haskell-src-exts} has 46 different constructors, while the
|Expr| type used by GHC Core only has 10!

\item Second, the GHC Core goes through multiple passes. Many of the passes
simplify the expressions in the source code, which in turns facilitates our
analysis. Consider the following example.

\begin{code}
jibble :: [Int] -> Int
jibble []        = 1
jibble (x : xs)  = wiggle x xs

wiggle :: Int -> [Int] -> Int
wiggle x xs = x * jibble xs + 1
\end{code}

Here, it is quite infeasible to recognise a foldr pattern prior to the inlining
of wiggle. However, once wiggle is inlined, it becomes quite clear that this is
a perfect match for our detector.

\item Finally, GHC Core is fully typed. This means we have access to type
information everywhere, which we can use in the analysis. While this is not
essential to our detector, it allows greater performance. Consider the simple
function add:

\begin{code}
add :: Int -> Int -> Int
add x y = x + y
\end{code}

Since no fold function will be associated to the |Int| datatype, we can
immediately skip analysing this function.

\end{itemize}

However, we must note that there is a major drawback to analyzing GHC Core
instead of Haskell code: it becomes much harder to use the results for
refactoring: in order to do refactoring, we would need an \emph{annotated}
expression type so the Core expressions can be traced back to the original
Haskell code. When we rewrite the Core expressions, the Haskell code must be
updated accordingly. This falls outside of the scope of this work.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The GHC Plugins system}
\label{subsection:ghc-plugins}

In GHC 7.2.1, a new mechanism to manipulate and inspect GHC Core was introduced
\cite{ghc-plugins}. After careful consideration, we adopted this approach
because it turned out to be much more accessible compared to directly using the
GHC API.

To be more precise, most Haskell libraries and applications today use the Cabal
build system \cite{cabal}. If we want to examine such a package for folds, it is
simply a matter of patching the Cabal file to include our plugin.

Using this mechanism, our plugin can manipulate expressions, in the form of an
algebraic datatype, directly. We show a simplified expresssion type here:

\ignore{
\begin{code}
data Id = Id
data Literal = Literal
data AltCon = AltCon
\end{code}
}

\begin{code}
data Expr
    = Var Id
    | Lit Literal
    | App Expr Expr
    | Lam Id Expr
    | Let Bind Expr
    | Case Expr Id [Alt]

data Bind
    = NonRec Id Expr
    | Rec [(Id, Expr)]

type Alt = (AltCon, [Id], Expr)
\end{code}

|Id| is the type used for different kinds of identifiers. |Lit| is any kind of
literal. |App| and |Lam| are well-known from the $\lambda$-calculus and
represent function application and lambda abstraction respectively. |Let| is
used to introduce new recursive or non-recursive binds, and |Case| is used for
pattern matching -- the only kind of branching possible in GHC Core.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}

%-------------------------------------------------------------------------------
\subsection{Identifying Folds}
\label{subsection:identifying-folds}

In order to test the quality of our fold discovery algorithm, we have applied
it to 13 popular Haskell packages. This experiment also provides us with an
estimate (a lower bound) of the number of explicitly recursive catamorphisms
that experienced Haskell programmers write in practice.

Table \ref{tabular:project-results} lists the results of the fold analysis on the left. The
first column lists the names of the packages and the second column (Total)
reports the total number of discovered catamorphisms. The third and fourth
column split up this total number in catamorphisms over lists (List) and
catamorphisms over other algebraic datatypes (Other). The fifth column (V.
arg.) shows the number of catamorphisms with auxiliary variable arguments
(e.g., left folds). The sixth column (N. rec.) counts the number of variable argument
catamorphisms with nested recursive calls such as the |f vs (f vs (v + acc))| example
from Section~\ref{}.

Finally, the last column provides the analysis results of
\emph{hlint}~\cite{hlint} for comparison. This tool provides hints on
how to refactor Haskell source code. The listed results reflect the number of
suggestions on the use of |map|, |filter| and |foldr| rather than explicit
recursion.

We see that across all packages our analysis finds more list catamorphisms than
hlint. In fact, our tool discovers some list catamorphisms in hlint's own
source code that hlint cannot find itself. Moreover, in addition to the results
in the table, our tool also successfully identifies all the list folds in the
hlint test suite.  There are three other packages in which hlint does not find
any catamorphisms. This is likely due to the fact that the authors of those
packages have themselves used hlint to discover and eliminate explicit
recursion.

We attribute the better results of our tool partly to the fact that more
catamorphisms are exposed in the core representation by GHC's program
transformations.  However, to a large extent, the better results are due to the
fact that our analysis is more powerful than that of hlint.  Also, hlint does
not look for catamorphisms over other datatypes than lists, while several
packages do have a significant number of those.

\begin{table*}
\begin{center}
\ra{1.3}
\begin{tabular}{@@{}lrrrrrrrrrrr@@{}}
\toprule
                 & \multicolumn{6}{c}{\textbf{folds}} &
                 & \multicolumn{4}{c}{\textbf{builds}} \\
\cmidrule{2-7} \cmidrule{9-12}
\textbf{Package} & \textbf{Total} & List & Other & V. arg. & N. rec. & \textbf{HLint} &
                 & \textbf{Total} & List & Other & Rec. \\
\midrule
Cabal-1.16.0.3          & 20  & 11  & 9   & 6   & 0   & 9  & & 101 & 81  & 20  & 5  \\
containers-0.5.2.1      & 100 & 11  & 89  & 41  & 11  & 1  & & 25  & 2   & 23  & 12 \\
cpphs-1.16              & 5   & 2   & 3   & 3   & 0   & 1  & & 6   & 5   & 1   & 3  \\
darcs-2.8.4             & 66  & 65  & 8   & 1   & 0   & 6  & & 354 & 354 & 0   & 26 \\
ghc-7.6.3               & 327 & 216 & 111 & 127 & 9   & 26 & & 480 & 178 & 302 & 53 \\
hakyll-4.2.2.0          & 5   & 1   & 4   & 3   & 0   & 0  & & 22  & 18  & 4   & 2  \\
haskell-src-exts-1.13.5 & 37  & 11  & 26  & 15  & 0   & 2  & & 140 & 74  & 66  & 16 \\
hlint-1.8.44            & 6   & 3   & 3   & 1   & 0   & 0  & & 69  & 62  & 7   & 1  \\
hscolour-1.20.3         & 4   & 4   & 0   & 0   & 0   & 2  & & 33  & 33  & 0   & 2  \\
HTTP-4000.2.8           & 6   & 6   & 0   & 2   & 0   & 3  & & 11  & 11  & 0   & 5  \\
pandoc-1.11.1           & 15  & 15  & 0   & 1   & 0   & 2  & & 97  & 97  & 0   & 16 \\
parsec-3.1.3            & 3   & 3   & 0   & 1   & 0   & 0  & & 10  & 10  & 0   & 0  \\
snap-core-0.9.3.1       & 4   & 3   & 1   & 1   & 0   & 0  & & 4   & 4   & 0   & 0  \\
\bottomrule
\end{tabular}
\caption{Results of identifying folds and builds in well-known Haskell packages}
\label{tabular:project-results}
\end{center}
\end{table*}

Folds with a variant arguments (left folds) are found quite regularly in
Haskell packages, but those with nested recursive calls are much rarer. We have
only found them in the GHC and containers packages; they may be an indication
of a rather advanced programming style.

\tom{What can we say about \#folds/LoC ratio?}
\tom{Perform same experiment on FLP project.}

%-------------------------------------------------------------------------------
\subsection{Identifying builds}

The right-hand side of Table~\ref{tabular:project-results} shows the result of
the build analysis for the 13 packages. The Total column lists the total number
of builds per package, while the List and Other columns split up this number
into list builds and builds of other datatypes. Column Rec show the number of
recursive builds.

Our main
observation is that the numbers are roughly proportional to those of the folds.
Unlike for folds, we are not aware of any other tool that detects builds and would
provide a basis for comparison.

%-------------------------------------------------------------------------------
\subsection{Optimization results}

\tom{We need to specifically address what happens to functions that are both
     a fold and a build like |map| and |filter|.}

\tom{We need to benchmark foldr/build examples from the literature.}

%===============================================================================
\section{Limitations}

Our approach is currently limited to directly recursive functions that recurse
over basic regular datatypes. Below we describe a number of cases that are not handled.

%-------------------------------------------------------------------------------
\paragraph{Mutually Recursive Functions}
Our approach currently does not deal with mutually recursive functions like:
\begin{code}
concat []      = []
concat (x:xs)  = concat' x xs

concat' []     xs  = concat xs
concat' (y:ys) xs   = y : concat' ys
\end{code}
which can be rewritten as:
\begin{code}
concat l = build (g l)

concat' x xs = build (g' x xs)

g l c n = foldr (\x xs -> foldr c xs x) n l

g' l xs c n = foldr c (g xs c n) l
\end{code}
An important special case of the above situation is that where one function is
a local definition of the other.
\tom{This happens in practice with our tool.}

%-------------------------------------------------------------------------------
\paragraph{Mutually Recursive Datatypes}

Mutually recursive functions arise naturally for mutually recursive datatypes like
rose trees. For instance,
\begin{code}
data Rose   = Node Int Forest
data Forest = Nil | Cons Rose Forest

sizeR (Node _ f)  = 1 + sizeF f

sizeF Nil         = 0
sizeF (Cons r f)  = sizeR r + sizeF f
\end{code}
can be written as
\begin{code}
data Rose   = Node Int Forest
data Forest = Nil | Cons Rose Forest

sizeR = foldR (\x f -> 1 + f) 0 (\r f -> r + f) 
sizeF = foldF (\x f -> 1 + f) 0 (\r f -> r + f)
\end{code}
where the two mutually recursive datatypes have the following signatures for their
fold functions:
\begin{code}
foldR  :: (Int -> f -> r) -> f -> (r -> f -> f) -> Rose    -> r 
foldF  :: (Int -> f -> r) -> f -> (r -> f -> f) -> Forest  -> f
\end{code}

%-------------------------------------------------------------------------------
\paragraph{GADTs}
GADTs pose an additional challenge because they represented
a family of types whose members are selected by means of a one or more type indices.
For instance, the GADT |Expr a| represents a family of expression types
by means of the type index |a|.
\begin{code}
data Expr a where
  Lit :: Int -> Expr Int
  Add :: Exp Int -> Exp Int -> Exp Int
  Eq  :: Exp Int -> Exp Int -> Exp Bool

eval :: Expr a -> a
eval (Lit n)    = n
eval (Add x y)  = eval x + eval y
eval (Eq x y)   = eval x == eval y
\end{code}

This type indexing is reflected in both the fold and build definitions.
%{
%format . = "."
\begin{code}
foldE  ::  (Int -> r Int) 
       ->  (r Int -> r Int -> r Int) 
       ->  (r Bool -> r Bool -> r Bool) 
       ->  Exp a -> r a
foldE lit add eq e = go e
  where 
   go (Lit n)    = lit n
   go (Add x y)  = add (go x) (go y)
   go (Eq x y)   = eq (go x) (go y)

buildExp :: (forall r  .   (Int -> r Int) 
                       ->  (r Int -> r Int -> r Int) 
                       ->  (r Int -> r Int -> r Bool) 
                       ->  r a) -> Exp a
buildExp g = g Lit Add Eq
\end{code}
%}

%{
%format . = "."
\begin{code}
eval e = 
  runR $ foldE  (\n -> R n) 
                (\x y -> R (runR x + runID y)) 
                (\x y -> R (runR x == runR y) 
                e

newtype R a = R { runR :: a }

foldE  ::  (Int -> r Int) 
       ->  (r Int -> r Int -> r Int) 
       ->  (r Bool -> r Bool -> r Bool) 
       ->  Exp a -> r a
foldE lit add eq e = go e
  where 
   go (Lit n)    = lit n
   go (Add x y)  = add (go x) (go y)
   go (Eq x y)   = eq (go x) (go y)

buildExp :: (forall r  .   (Int -> r Int) 
                       ->  (r Int -> r Int -> r Int) 
                       ->  (r Int -> r Int -> r Bool) 
                       ->  r a) -> Exp a
buildExp g = g Lit Add Eq
\end{code}
%}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

%-------------------------------------------------------------------------------
\subsection{Applications of Folds and Fusion}

There is a long line of work on writing recursive functions in terms of
structured recursion schemes, as well as proving fusion properties of these and
exploiting them for deriving efficient programs. Typically the derivation
process is performed manually.

Bird and Meertens~\cite{bird,meertens} have come up with several equational
laws for recursion schemes to serve them in their work on program calculation.
With their Squiggol calculus, Meijer et al.~\cite{meijer1991} promote the use
of structured recursion by means of recursion operators. These operators are
defined in a datatype generic way and are equipped with a number of algebraic
laws that enable equivalence-preserving program transformations.

Gibbons~\cite{Gibbons2003:Origami} promotes explicit programming in terms of
folds and unfolds, which he calls \emph{origami} programming. Unfolds are the dual
of folds, and capture a special case of builds.

Gill et al.~\cite{gill1993} present the foldr/build fusion rule and discuss
its benefits. They mention that it would be desirable, yet highly challenging,
for the compiler to notice whether functions can be expressed in terms of |foldr|
and |build|. That would allow programmers to write programs in whatever style they like.

%-------------------------------------------------------------------------------
\subsection{Automation}

Higher-order matching is a general technique for matching expressions in
functional programs against expression templates. In the context of Haskell,
Sittampalam and de Moor~\cite{mag} have applied higher-order matching in their
rewriting system, called MAG. They have used MAG for fusion in the following
way. the programmer specifies the initial program, a specficiation of the
target program and suitable rewrite rules. The latter includes a rule for
|foldr| fusion: 
%{
%format . = "."
\begin{spec}
f (foldr c n l) = foldr c' n' l
   if  f n = n'
       forall x y. f (c x y) = c' x (f y) 
\end{spec}
%}
Then the MAG system will attempt to derive the target implementation by
applying the rewrite rules. Finally, the programmer needs to check whether MAG
has only applied the fusion rule to strict functions |f|, a side condition of
the fusion rule that cannot be specified in MAG.

GHC rewrite rules~\cite{jones2001} are a lightweight way to (semi-)automate fusion. The
programmer provides rewrite rules to rewrite program patterns into their fused
forms and the compiler applies these whenever it finds an opportunity.  The one
part that is not automated is that programmers still have to write their code
in terms of the higher-order recursion schemes. GHC has set up various of its
base libraries in this way to benefit from fold/build fusion among others.

Building on GHC rewrite rules, Coutts et al.~\cite{coutts2007} have proposed
stream fusion as a convenient alternative to foldr/build fusion. Stream fusion
is able to fuse zips and left folds, but, on the downside, it is less obvious
for the programmer to write his functions in the required style.  Hinze et
al.~\cite{hinze} provide clues for how to generalize stream fusion: by expressing
functions in terms of an unfold, followed by a natural transformation and a
fold.

%  filter p l
%     = build (\c n -> foldr (\x r -> if p x then c x r else r) n l)

% foldr f z $ filter () $ build g
%
%    g (\ x xs -> if p x then f x xs else xs) z

% zip []     l  = []
% zip (x:xs) l  =
%   case l of 
%     []      -> []
%     (y:ys)  -> (x,y) : zip xs ys

% zip l1 l2 = foldr (\x xs l2 -> case l2 of { [] -> [] ; (y:ys) -> (x,y) : xs ys}) (\l2 -> []) l1 l2


%% It would be interesting future work to automatically identify such
%% patterns.

% However, at
% the time of writing, there is no known reliable method of optimising uses of
% |concatMap|. |concatMap| is important because it represents the entire class of
% nested list computations, including list comprehensions~\cite{coutts2010}.

The \emph{hlint}~\cite{hlint} tool is designed to recognize various code
patterns and offer suggestions for improving them. In particular, it recognizes
various forms of explicit recursion and suggests the use of appropriate
higher-order functions like |map|, |filter| and |foldr| that capture these
recursion patterns.  As we already showed in Section
\ref{subsection:identifying-folds}, we are able to detect more instances of
folds for Haskell lists than hlint. Moreover, hlint makes no effort to detect
folds for other algebraic datatypes.

Supercompilation~\cite{supercompilation} is a much more generic and brute-force
technique for program specialization that is capable of fusing
producer-consumer pipelines.  Unfortunately, the current state of the art of
supercompilation for Haskell~\cite{UCAM-CL-TR-835} is still too unreliable to
be used in practice.

\begin{itemize}
\item fold applications
\item datatypes a la carte
\item attribute grammars
\end{itemize}

%===============================================================================
\section{Conclusion}

\tom{mention mutually recursive ADTs as important future work}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \appendix
% \section{Appendix Title}
% 
% This is the text of the appendix, if you need one.
% 
% \acks
% 
% Acknowledgments, if needed.

% References
\bibliographystyle{abbrvnat}
\bibliography{references}

\end{document}
