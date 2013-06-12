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
Programs written in terms of higher-order recursion schemes like |foldr| and
|build| can benefit from program optimization like short-cut fusion.
Unfortunately, programmers often avoid these schemes in favor of explicitly
recursive functions.

This paper shows how programmers can continue to write programs in their
preferred explicitly recursive style and still benefit from fusion. It presents
syntactic algorithms to automatically find and expose instances of |foldr| and
|build|. The algorithms have been implemented as GHC compiler passes and deal
with all regular algebraic datatypes, not just lists. A case study demonstrates
that these passes are effective at finding many instances in popular Haskell
packages.


% Rewriting explicitly recursive functions in terms of higher-order functions such
% as |fold| and |map| brings many advantages such as conciseness, improved
% readability, and it facilitates some optimisations. However, it is not always
% straightforward for a programmer to write functions in this style. We present an
% approach to automatically detect these higher-order functions, so the programmer
% can have his cake and eat it, too.
\end{abstract}

% TODO: Explicit results, evaluation

% \category{CR-number}{subcategory}{third-level}

% \terms
% Language

\keywords
catamorphisms, fold/build fusion, analysis, transformation 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}\label{s:intro}

Higher-order functions are immensely popular in Haskell, whose Prelude alone
offers a wide range of them (e.g., |map|, |filter|, |any|, \ldots). This is not
surprising, because they are the key \emph{abstraction} mechanism of functional
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
of explicit recursion in his functions, like
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
\item We provide a GHC compiler plugin\footnote{\url{http://github.ugent.be/javdrjeu/what-morphism}} that performs these detections and
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
\section{Overview}\label{s:overview}

This section briefly reviews folds, builds and fusion to prepare for the next
sections, that provide systematic algorithms for finding folds and builds in
explicitly recursive functions.

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
\subsection{Folds}\label{s:overview:fold}

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
The intermediate steps can of course be skipped in practice and
our algorithm in Section~\ref{s:fold} does so.

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

The above ideas for folds of lists easily generalize to other inductively
defined algebraic datatypes.  We illustrate that on leaf trees.
\begin{code}
data Tree a
    =  Leaf a
    |  Branch (Tree a) (Tree a)
\end{code}

The |sumTree| function is an example of a directly recursive catamorphism
over leaf trees.
\begin{code}
sumTree :: Tree Int -> Int
sumTree (Leaf x)      = x
sumTree (Branch l r)  = sumTree l + sumTree r
\end{code}
This catamorphic recursion scheme can be captured in a fold function too.
The generic idea is that a fold function transforms the inductive datatype
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

The fold over leaf trees enables us to define |sumTree| succinctly as
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
\subsection{Builds}\label{s:overview:build}

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
        | n <= 0     = nil
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
buildT  ::  (forall b. (a -> b) -> (b -> b -> b) -> b)
        ->  Tree a
buildT g = g Leaf Branch
\end{code}
%}

With this build function we can express a producer of leaf trees
\begin{code}
range :: Int -> Int -> Tree a
range l u
  | u > l      =  let m = l + div (u - l) 2
                  in  Branch (range l m) (range (m+1) u)
  | otherwise  =  Leaf l
\end{code}
as a build:
\begin{code}
range l u  = 
  buildT (\leaf branch -> 
    let g l u
          | u > l      =  let m = l + div (u - l) 2
                          in  branch (g l m) (g (m+1) u)
          | otherwise  =  leaf l
    in g l u)
\end{code}

%-------------------------------------------------------------------------------
\subsection{Fold/Build Fusion}\label{s:overview:fusion}

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
sumOfSquaredOdds :: Int -> Int
sumOfSquaredOdds = 
  sum . map (^ 2) . filter odd . enumFromTo 1
\end{code}
This code is quite compact and easy to compose from existing library functions.
However, when compiled naively, it is also rather inefficient because it
performs four loops and allocates three intermediate lists (the results of
respectively |enumFromTo 1|, |filter odd| and |map (^ 2)|) that are immediately
consumed again.

With the help of fusion, whole pipelines like |sumOfSquaredOdds| can be
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
\[ |foldT leaf branch (buildT g)| ~~ |==| ~~ |g leaf branch| \]

It is key to fusing two loops into one:
\begin{spec}
    sumTree (range l u)

== {- inline |sumTree| -}

    foldT id (+) (range l u)

== {- inline |range| -}

    foldT id (+) (buildT $ \leaf branch ->
        let g l u
		| u > l      =  let m = l + div (u - l) 2
		                in  branch (g l m) (g (m+1) u)
		| otherwise  =  leaf l
        in g l u)

== {- fold/build fusion -}

    (\leaf branch ->
        let g l u
		| u > l      =  let m = l + div (u - l) 2
		                in  branch (g l m) (g (m+1) u)
		| otherwise  =  leaf l
        in g l u) id (+)

== {- $\beta$-reduction -}

    let g l u
    	| u > l      =  let m = l + div (u - l) 2
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
  GHC does not explicitly cater for other datatypes than lists.
  While the programmer can replicate the existing list infrastructure for his
  own datatypes, it requires a considerable effort and rarely happens in practice.
\item
  Programmers or libraries need to explicitly define their functions
  in terms of |foldr| and |build|. If they don't, then fusion is not possible.
  This too turns out to be too much to ask as we see many uses of explicit
  recursion in practice (see Section~\ref{s:evaluation}).
\end{enumerate}

This work addresses both limitations. It allows programmers to write their
functions in explicitly recursive style and performs fold/build fusion for any
directly inductive datatype.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Finding Folds}\label{s:fold}
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
  { |e'1| = [|y| \mapsto |[]|]|e1| \\ |f| \not\in \mathit{fv}(|e1|) \\ |ws|~\textit{fresh} \\\\ 
    |e2|~{}_{|vs|}\!\!\stackrel{|f triangle|}{\leadsto}_{|ws|} |e'2| \\ \{ f, x, vs \} \cap \mathit{fv}(|e'2|) = \emptyset
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

\paragraph{Folds with Parameters}\tom{Explain better the accumulating parameters.}
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
\section{Finding Builds}\label{s:build}

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
\section{Implementation}\label{s:implementation}

Rather than to implement our algorithms as a source-level program
transformation, we have implemented our algorithms as compiler passes in a
plugin~\cite{ghc-plugins} for GHC. This has three important advantages:
\begin{itemize}
\item Firstly, the compiler passes work with GHC's core representation, which is
      much simpler than Haskell source syntax. For instance, the type
      that represents Haskell source expressions in the popular \texttt{haskell-src-exts} 
      package features 46 different constructors, while the corresponding GHC core
      type has only 10.

\item Secondly, GHC optimizer performs various beneficial transformation passes on a program's
      core representation before running our algorithms. Many of these passes
      help our algorithms by simplifying the source code.
      Consider the following example of two mutually recursive functions.

\begin{code}
f :: [Int] -> Int
f []        = 1
f (x : xs)  = g x xs

g :: Int -> [Int] -> Int
g x xs = x * f xs + 1
\end{code}
      Our fold finding algorithm does not identify |f| as a catamorphism, because it
      does not see the recursive call, which is hidden in |g|.  However, GHC's
      inlining pass is likely to inline |g| in the body of |f| and thus expose the
      recursive call. 
   
      In other words, we can keep our algorithms relatively simple, because other GHC
      passes already do part of the work for us.
    
      \tom{Discuss alternative: new fold-specific rule for the algorithm}

\item Finally, GHC core is fully typed. While type information is not essential,
      our algorithms can make good use of it to improve their peroformance. Consider this simple function:
\begin{code}
add :: Int -> Int -> Int
add x y = x + y
\end{code}
The type signature reveals that none of the parameters is an inductively
defined datatype, nor is the result type. As a consequence, without looking a
the function body, our algorithms can conclude that the function cannot be
expressed as a fold or a build.

\end{itemize}

%-------------------------------------------------------------------------------
\subsection{Algorithm Implementation}

We have implemented the two algorithms as separate passes in our plugin. The
implementations deviate from the non-deterministic algorithms of Sections
\ref{s:fold} and \ref{s:build} on two accounts:
\begin{itemize}
\item They deal with the core language, which is slightly larger than the
      language used earlier. As already indicated, core carries type information, 
      which our implementation must adjust when performing the transformation.
      Core also involves local binders in addition to toplevel binders. We
      analyze these too for occurrences of folds and builds.

\item Our implementation is of course deterministic rather than
      non-deterministic, and, as described above, based on the available type
      information, it tries to fail fast.
\end{itemize}

Below are two more important points with respect to the quality of obtained
fusions.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Local Generator Binders}

An important point for the |build| finding algorithm is that the new abstract
generator function is actually introduced as a local binding, rather than a new
toplevel binding. The reason is that we want GHC to specialize the generator function
at the use site after fusion.

For instance, after the inlining and fusion of |sum (replicate n)|, we get |g
(+) 0| where |g| is the abstract generator function. If |g| is defined with a
toplevel binder, GHC will not inline it because it is recursive. Hence, while
the intermediate datastructure has been eliminated, we still pay the price of
the generator's abstraction.

However, if |g| is actually defined locally in |replicate|, as shown in
Section~\ref{s:overview:build}, GHC can easily specialize the recursive definition of the
generator and eliminate the abstraction. The result is a tight first-order
loop.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Relative Pass Scheduling}
As we have already argued in Section~\ref{s:overview:fusion}, it is crucial for the fusion
of pipelines that transformation functions are expressed as a build of a fold.
In order to obtain this required form, our build finding pass must be scheduled
before the fold finding pass. Only in this order do we obtain, e.g., the definition
\begin{spec}
map f l = build (\c n -> foldr (\x xs -> c (f x) xs) n l)
\end{spec}
If we first find the fold, we get stuck at the following intermediate form
\begin{spec}
map f l = foldr (\x xs -> f x : xs) [] l
\end{spec}
because our build finder is not equipped to deal with folds.

%-------------------------------------------------------------------------------
\subsection{Fusion}

The passes for finding folds and builds are inherently compatible with GHC's
approach to list fusion. Whenever a list producer or consumer is rewritten into
a |foldr| or |build|, it becomes a possible subject of the GHC rewrite rules
that target these higher-order schemes.

Moreover, for fusion to happen it is not necessary for our passes to find a
fold and a build together. Fusion can also happen when the programmer combines,
e.g., his own explicitly recursive catamorphism with a library function that is
already expressed as a build. 

\tom{an example?}

%-------------------------------------------------------------------------------
\subsection{Datatype Support}

In order to introduce calls to fold and build functions for a datatype, these 
functions have to be available for that datatype. At present, GHC only provides
such functions for lists.

In order to support additional datatypes, we allow the programmer to register
fold and build functions for his own datatypes by means of
annotations~\cite{ghc-annotations}. For instance, the following annotation
does so for the type of leaf trees.
\begin{Verbatim}
{-# ANN type Tree 
     (RegisterFoldBuild "foldT" "buildT") 
  #-}
\end{Verbatim}
 
Moreover, we also provide complimentary 
Template Haskell~\cite{sheard2002} routines to derive the implemenations of the two functions.
%{
%format Tree = "`Tree"
\begin{spec}
$(deriveFold Tree "foldT")
$(deriveBuild Tree "buildT")
\end{spec}

Similarly, to support fusion for other datatypes, we follow GHC's rewriting
rules approach for lists. However, instead of having to write the fusion rewrite
rule explicitly, we provide a handy Tempate Haskell routine. For instance,
\begin{spec}
$(deriveFusion Tree "foldT" "buildT")
\end{spec}
%}
generates
\begin{Verbatim}
{-# "foldT/buildT-fusion"
   forall l b 
    (g :: forall b. (a -> b) -> (b -> b -> b) -> b). 
   foldT l n (buildT g) = g l b
  #-}
\end{Verbatim}

If desired, the responsability for registering types and generating the
higher-order schemes and rewrite rules can easily be moved to the compiler. At
this time, and for the purpose of evaluation, it suits us to have a bit more
control.

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \subsection{The GHC Core language}
% \label{subsection:ghc-core}
% 
% We already gave a brief, high-level explanation of the Core language in section
% \ref{section:core-expressions}. In the next few sections, we explain how we
% obtain and manipulate this language in practice.
% 
% GHC \cite{ghc} is the de-facto compiler for Haskell, altough some alternatives
% exist. We selected GHC as target for our implementation because of this reason.
% 
% By choosing GHC, we have two convenient representations of Haskell code at our
% disposal for analsis.
% 
% The most straightforward representation is the Haskell source code itself.
% There are numerous parsing libraries to make this task easier
% \cite{haskell-src-exts}.
% 
% However, during compilation, the Haskell code is transformed to the GHC Core
% \cite{tolmach2009} language in a number of passes.
% 
% The latter is particulary interesting for our purposes. It offers the following
% advantages over regular Haskell source code:
% 
% However, we must note that there is a major drawback to analyzing GHC Core
% instead of Haskell code: it becomes much harder to use the results for
% refactoring: in order to do refactoring, we would need an \emph{annotated}
% expression type so the Core expressions can be traced back to the original
% Haskell code. When we rewrite the Core expressions, the Haskell code must be
% updated accordingly. This falls outside of the scope of this work.
% 
% 
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \subsection{The GHC Plugins system}
% \label{subsection:ghc-plugins}
% 
% In GHC 7.2.1, a new mechanism to manipulate and inspect GHC Core was introduced
% \cite{ghc-plugins}. After careful consideration, we adopted this approach
% because it turned out to be much more accessible compared to directly using the
% GHC API.
% 
% To be more precise, most Haskell libraries and applications today use the Cabal
% build system \cite{cabal}. If we want to examine such a package for folds, it is
% simply a matter of patching the Cabal file to include our plugin.
% 
% Using this mechanism, our plugin can manipulate expressions, in the form of an
% algebraic datatype, directly. We show a simplified expresssion type here:
% 
% \ignore{
% \begin{code}
% data Id = Id
% data Literal = Literal
% data AltCon = AltCon
% \end{code}
% }
% 
% \begin{code}
% data Expr
%     = Var Id
%     | Lit Literal
%     | App Expr Expr
%     | Lam Id Expr
%     | Let Bind Expr
%     | Case Expr Id [Alt]
% 
% data Bind
%     = NonRec Id Expr
%     | Rec [(Id, Expr)]
% 
% type Alt = (AltCon, [Id], Expr)
% \end{code}
% 
% |Id| is the type used for different kinds of identifiers. |Lit| is any kind of
% literal. |App| and |Lam| are well-known from the $\lambda$-calculus and
% represent function application and lambda abstraction respectively. |Let| is
% used to introduce new recursive or non-recursive binds, and |Case| is used for
% pattern matching -- the only kind of branching possible in GHC Core.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}\label{s:evaluation}

%-------------------------------------------------------------------------------
\subsection{Identifying Folds}

\begin{table}[t!]
\begin{center}
\ra{1.3}
\begin{tabular}{@@{}l@@{\hspace{0mm}}r@@{\hspace{2mm}}r@@{\hspace{2mm}}r@@{\hspace{2mm}}r@@{\hspace{2mm}}r@@{\hspace{2mm}}r@@{\hspace{2mm}}}
\toprule
\textbf{Package} & \textbf{Total} & List & Other & Acc. & N. rec. & \textbf{HLint} \\
\midrule
Cabal-1.16.0.3          & 20  & 11  & 9   & 6   & 0   & 9  \\
containers-0.5.2.1      & 100 & 11  & 89  & 41  & 11  & 1  \\
cpphs-1.16              & 5   & 2   & 3   & 3   & 0   & 1  \\
darcs-2.8.4             & 66  & 65  & 8   & 1   & 0   & 6  \\
ghc-7.6.3               & 327 & 216 & 111 & 127 & 9   & 26 \\
hakyll-4.2.2.0          & 5   & 1   & 4   & 3   & 0   & 0  \\
haskell-src-exts-1.13.5 & 37  & 11  & 26  & 15  & 0   & 2  \\
hlint-1.8.44            & 6   & 3   & 3   & 1   & 0   & 0  \\
hscolour-1.20.3         & 4   & 4   & 0   & 0   & 0   & 2  \\
HTTP-4000.2.8           & 6   & 6   & 0   & 2   & 0   & 3  \\
pandoc-1.11.1           & 15  & 15  & 0   & 1   & 0   & 2  \\
parsec-3.1.3            & 3   & 3   & 0   & 1   & 0   & 0  \\
snap-core-0.9.3.1       & 4   & 3   & 1   & 1   & 0   & 0  \\
\bottomrule
\end{tabular}
\caption{Folds found in well-known Haskell packages}
\label{tabular:project-results}
\end{center}
\end{table}
\label{subsection:identifying-folds}

% \begin{table*}[t!]
% \begin{center}
% \ra{1.3}
% \begin{tabular}{@@{}lrrrrrrrrrrr@@{}}
% \toprule
%                  & \multicolumn{6}{c}{\textbf{folds}} &
%                  & \multicolumn{4}{c}{\textbf{builds}} \\
% \cmidrule{2-7} \cmidrule{9-12}
% \textbf{Package} & \textbf{Total} & List & Other & Acc. & N. rec. & \textbf{HLint} &
%                  & \textbf{Total} & List & Other & Rec. \\
% \midrule
% Cabal-1.16.0.3          & 20  & 11  & 9   & 6   & 0   & 9  & & 101 & 81  & 20  & 5  \\
% containers-0.5.2.1      & 100 & 11  & 89  & 41  & 11  & 1  & & 25  & 2   & 23  & 12 \\
% cpphs-1.16              & 5   & 2   & 3   & 3   & 0   & 1  & & 6   & 5   & 1   & 3  \\
% darcs-2.8.4             & 66  & 65  & 8   & 1   & 0   & 6  & & 354 & 354 & 0   & 26 \\
% ghc-7.6.3               & 327 & 216 & 111 & 127 & 9   & 26 & & 480 & 178 & 302 & 53 \\
% hakyll-4.2.2.0          & 5   & 1   & 4   & 3   & 0   & 0  & & 22  & 18  & 4   & 2  \\
% haskell-src-exts-1.13.5 & 37  & 11  & 26  & 15  & 0   & 2  & & 140 & 74  & 66  & 16 \\
% hlint-1.8.44            & 6   & 3   & 3   & 1   & 0   & 0  & & 69  & 62  & 7   & 1  \\
% hscolour-1.20.3         & 4   & 4   & 0   & 0   & 0   & 2  & & 33  & 33  & 0   & 2  \\
% HTTP-4000.2.8           & 6   & 6   & 0   & 2   & 0   & 3  & & 11  & 11  & 0   & 5  \\
% pandoc-1.11.1           & 15  & 15  & 0   & 1   & 0   & 2  & & 97  & 97  & 0   & 16 \\
% parsec-3.1.3            & 3   & 3   & 0   & 1   & 0   & 0  & & 10  & 10  & 0   & 0  \\
% snap-core-0.9.3.1       & 4   & 3   & 1   & 1   & 0   & 0  & & 4   & 4   & 0   & 0  \\
% \bottomrule
% \end{tabular}
% \caption{Folds and builds found in well-known Haskell packages}
% \label{tabular:project-results}
% \end{center}
% \end{table*}
% \label{subsection:identifying-folds}

In order to test the quality of our fold finding algorithm, we have applied it
to 13 popular Haskell packages. We have not enabled any of GHC's optimization
flags and disabled the actual rewriting in our pass. In this way, we get an
accurate estimate (a lower bound) of the number of explicitly recursive
catamorphisms that experienced Haskell programmers write in practice.

Table \ref{tabular:project-results} lists the results of the fold analysis. The
first column lists the names of the packages and the second column (Total)
reports the total number of discovered catamorphisms. The third and fourth
column split up this total number in catamorphisms over lists (List) and
catamorphisms over other algebraic datatypes (Other). The fifth column (Acc.) shows the number of catamorphisms with 
accumulating parameters
(e.g., left folds). The sixth column (N. rec.) counts the number of accumulating parameter
catamorphisms with nested recursive calls such as the |f vs (f vs (v + acc))| example
from Section~\ref{s:overview:fold}.

Finally, the last column provides the analysis results of
\emph{hlint}~\cite{hlint} for comparison. This tool provides hints on
how to refactor Haskell source code. The listed results reflect the number of
suggestions on the use of |map|, |filter|, |foldl| and |foldr| rather than explicit
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

Folds with a variant arguments (left folds) are found quite regularly in
Haskell packages, but those with nested recursive calls are much rarer. We have
only found them in the GHC and containers packages; they may be an indication
of a rather advanced programming style.

% \tom{What can we say about \#folds/LoC ratio?}
% \tom{Perform same experiment on FLP project.}

%-------------------------------------------------------------------------------
\subsection{Identifying builds}
\label{subsection:identifying-folds}

\begin{table}[t!]
\begin{center}
\ra{1.3}
\begin{tabular}{@@{}lrrrr@@{}}
\toprule
\textbf{Package} & \textbf{Total} & List & Other & Rec. \\
\midrule
Cabal-1.16.0.3          & 101 & 81  & 20  & 5  \\
containers-0.5.2.1      & 25  & 2   & 23  & 12 \\
cpphs-1.16              & 6   & 5   & 1   & 3  \\
darcs-2.8.4             & 354 & 354 & 0   & 26 \\
ghc-7.6.3               & 480 & 178 & 302 & 53 \\
hakyll-4.2.2.0          & 22  & 18  & 4   & 2  \\
haskell-src-exts-1.13.5 & 140 & 74  & 66  & 16 \\
hlint-1.8.44            & 69  & 62  & 7   & 1  \\
hscolour-1.20.3         & 33  & 33  & 0   & 2  \\
HTTP-4000.2.8           & 11  & 11  & 0   & 5  \\
pandoc-1.11.1           & 97  & 97  & 0   & 16 \\
parsec-3.1.3            & 10  & 10  & 0   & 0  \\
snap-core-0.9.3.1       & 4   & 4   & 0   & 0  \\
\bottomrule
\end{tabular}
\caption{Builds found in well-known Haskell packages}
\label{tabular:build-results}
\end{center}
\end{table}

Table~\ref{tabular:build-results} shows the results of the build analysis for
the 13 packages. The Total column lists the total number of builds per package,
while the List and Other columns split up this number into list builds and
builds of other datatypes. Column Rec show the number of recursive builds.

Our main
observation is that the numbers are roughly proportional to those of the folds.
Unlike for folds, we are not aware of any other tool that detects builds and would
provide a basis for comparison.

%-------------------------------------------------------------------------------
\subsection{Fusion}

We have not measured any significant performance improvements in the above 13
packages. Likely, the critical paths in thse packages have already been
optimized by their authors.

Hence, instead, we offer the following aritificial benchmarks, that demonstrate
the potential impact of fusion on program runtime.  We have two similar sets of
benchmarks, one for lists and one for leaf trees, that consist of pipelines
of increasing length. The $i$the benchmark consists of a producer (|upto|), followed by
|i-1| transformers (|map (+1)| and a final consumer (|sum|). Each of the components of 
the pipeline is defined in an explicitly recursive style (see Fig.~\ref{f:pipeline:components}).

%format l1
%format l2
%format l3
%format l4
%format l5
%format t1
%format t2
%format t3
%format t4
%format t5
%format elapsed = "\ldots"


We have timed the pipelines with Criterion~\cite{criterion}, using input $n =
100\,000$.  Each of the benchmarks was compiled (and run) twice: once with the
\texttt{-O2 -fenable-rewrite-rules} GHC flags, and once with those two flags
and our compiler passes. 
We have inspected the produced core code and observed that in the former case the
pipeline is not fused at all, and in the latter case it is fully fused. For instance,
the fully fused code obtained for |l5| is:
\begin{spec}
l5 = 
  \l u -> case l > u of                                       
            False  -> case l5 (l + 1) u of                    
                         n -> ((((l + 1) + 1) + 1) + 1) + n   
            True   -> 0                                   
\end{spec}

Figures~\ref{figure:list-speedups} and \ref{figure:tree-speedups}
show the absolute runtimes and the speed-ups obtained by fusion for respectively the
list and tree pipelines.
The relative speed-ups are defined as $(t_u - t_f)/t_u$ where $t_u$ is the runtime
of the unfused pipelines and $t_f$ the runtime of the fused pipelines.

We see in the unoptimized version that the shortest list pipeline |l1| has a
base runtime of about 10ms; every additional transformation in the longer
pipelines adds about 4ms. Our compiler passes cause big-speeds. Firstly, the
base runtime is recuded by almost 80\%. Moreover, the cost of the additional
transformations is completely eliminated: all pipelines have the same absolute runtime.
This means that the relative speed-up gradually converges to 100\%.
Similar observations can be made for the leaf tree pieplines.

\begin{figure}[h!]
\includegraphics[width=0.50\textwidth]{plots/list.pdf}

\includegraphics[width=0.50\textwidth]{plots/list-speedups.pdf}
\caption{Absolute runtimes (top) and relative speed-ups (bottom) for list pipelines.}
\label{figure:list-speedups}
\end{figure}

\begin{figure}[h!]
\includegraphics[width=0.50\textwidth]{plots/tree.pdf}
\includegraphics[width=0.50\textwidth]{plots/tree-speedups.pdf}
\caption{Absolute runtimes (top) and relative speed-ups (bottom) for leaf tree pipelines.}
\label{figure:tree-speedups}
\end{figure}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}\label{s:related}


%-------------------------------------------------------------------------------
\subsection{Folds and Fusion}

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

Various authors have investigated variants of short-cut fusion where
datastructures are produced and consumed in the context of some computational
effect.  Andres et al.~\cite{} consider the case where the effect modeled by an
applicative functor, and both Ghani \& Johan~\cite{ghani} and Manzino \&
Pardo~\cite{manzino} tackle monadic effects. It would be interesting
to extend our approach to finding uses of their effectful recursion schemes.

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

%===============================================================================
\section{Discussion}\label{s:discussion}

We have presented a syntactic approach to transforming explicilty recursive
functions into invocations of higher-order recursion schemes (folds and builds
in particular). Our experimental evaluation shows that this technique is
effective at finding many such occurrences in popular Haskell packages written
by experienced programmers.

Our work currently targets the most common case: directly recursive functions
over directly recursive regular datatypes. In future work it would be
interesting to extend this class to encompass a wider range, although we expect
diminishing returns.

%-------------------------------------------------------------------------------
\paragraph{Mutually Recursive Functions}
Our approach does not deal with mutually recursive functions like:
\begin{code}
concat :: [[a]] -> [a]
concat []      = []
concat (x:xs)  = concat' x xs
  where
    concat' :: [a] -> [[a]] -> [a]
    concat' []     xs  = concat xs
    concat' (y:ys) xs   = y : concat' ys xs
\end{code}
which is ideally rewritten to:
\begin{code}
concat l = build (\c n -> foldr (\x xs -> foldr c xs x) n l)
\end{code}
but the mutual recursion obscures the |build|, and instead we get:
\begin{code}
concat l = foldr (\x xs -> foldr (:) xs x) [] l
\end{code}
In order to solve this problem, the |build| finding algorithm should be
extended to handle mutually recursive groups. 

%-------------------------------------------------------------------------------
\paragraph{Mutually Recursive Datatypes}

Mutually recursive functions arise naturally for mutually recursive datatypes,
which are common representations for abstract syntax trees and document
structures. A simple example are rose trees:
\begin{code}
data Rose   = Node Int Forest
data Forest = Nil | Cons Rose Forest

sizeR :: Rose -> Int
sizeR (Node _ f)  = 1 + sizeF f

sizeF :: Forest -> Int
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
a family of types whose members are selected by means of one or more type indices.
For instance, the GADT |Expr a| represents a family of expression types
by means of the type index~|a|.
\begin{code}
data Expr a where
  Lit :: Int -> Expr Int
  Add :: Exp Int -> Exp Int -> Exp Int
  Eq  :: Exp Int -> Exp Int -> Exp Bool
\end{code}

This type indexing is carried over to the type signatures of its fold and build
definitions~\cite{Johann:2008:FSP:1328438.1328475},
where |Expr :: * -> *| is abstracted to |r :: * -> *|.
%{
%format . = "."
\begin{spec}
foldE  ::  (Int -> r Int) 
       ->  (r Int -> r Int -> r Int) 
       ->  (r Bool -> r Bool -> r Bool) 
       ->  Exp a -> r a

buildExp :: (forall r  .   (Int -> r Int) 
                       ->  (r Int -> r Int -> r Int) 
                       ->  (r Int -> r Int -> r Bool) 
                       ->  r a) -> Exp a
\end{spec}
%}

This means that when we rewrite a catamorphism like
\begin{code}
eval :: Expr a -> a
eval (Lit n)    = n
eval (Add x y)  = eval x + eval y
eval (Eq x y)   = eval x == eval y
\end{code}
into an invocation of |foldE|, we must come up with
an appropriate indexed type to instantiate |r|. In particular,
when the catamorphism does not feature such an indexed type, we
may have to introduce a new one:
%{
%format . = "."
\begin{code}
newtype R a = R { runR :: a }

eval e = 
  runR $ foldE  (\n -> R n) 
                (\x y -> R (runR x + runID y)) 
                (\x y -> R (runR x == runR y) 
                e
\end{code}
%}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \acks
% 
% Acknowledgments, if needed.

% References
\bibliographystyle{abbrvnat}
\bibliography{references}

\appendix
\section{Pipeline Benchmarks}

\begin{code}

-- List Pipelines

suml :: [Int] -> Int
suml []        = 0
suml (x : xs)  = x + suml xs

mapl :: (a -> b) -> [a] -> [b]
mapl f = go
  where
    go []        = []
    go (x : xs)  = f x : go xs

uptol :: Int -> Int -> [Int]
uptol lo up = go lo
  where
    go i
        | i > up     = []
        | otherwise  = i : uptol (i + 1) up

l1, l2, l3, l4, l5 :: Int -> Int
l1 n = suml (1 `uptol` n)
l2 n = suml (mapl (+ 1) (1 `uptol` n))
l3 n = suml (mapl (+ 1) (mapl (+ 1) (1 `uptol` n)))
l4 n = elapsed
l5 n = elapsed

-- Tree Pipelines

sumt :: Tree Int -> Int
sumt (Leaf x)      = x
sumt (Branch l r)  = sumt l + sumt r

mapt :: (a -> b) -> Tree a -> Tree b
mapt f = go
  where
    go (Leaf x)      = Leaf (f x)
    go (Branch l r)  = Branch (go l) (go r)

uptot :: Int -> Int -> Tree Int
uptot lo hi
    | lo >= hi   = Leaf lo
    | otherwise  =
        let mid = div (lo + hi) 2
        in Branch (uptot lo mid) (uptot (mid + 1) hi)

t1, t2, t3, t4, t5 :: Int -> Int
t1 n = sumt (1 `uptot` n)
t2 n = sumt (mapt (+ 1) (1 `uptot` n))
t3 n = sumt (mapt (+ 1) (mapt (+ 1) (1 `uptot` n)))
t4 n = elapsed
t5 n = elapsed
\end{code}

\end{document}
