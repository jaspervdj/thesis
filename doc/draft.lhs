\documentclass[preprint, 9pt]{sigplanconf}

%include polycode.fmt

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
programming languages. They enable capturing and reusing common patterns among,
often recursive, function definitions to a much larger extent than first-order
functions. In addition to the obvious code reuse and increased programmer
productivity, uses of higher-order functions have many other potential
advantages over conventional first-order definitions.
\begin{itemize}
\item Uses of higher-order functions can be more quickly understood because
      they reduce the that is already known pattern to a single name and thus draw
      the attention immediately to what is new (i.e., the function parameters).

\item Because the code is more compact and the number of bugs is proportional
      to code size~\cite{gaffney1984}, higher-order functions should lead to
      fewer bugs.

\item Properties can be established for the higher-order function indepently
      from its particular uses. This makes (e.g., equational) reasoning more productive.

\item Since properties and occurrences are more readily available, they make good targets
      for automatic optimization in compilers.
\end{itemize}

A particularly ubiquitous pattern is that of folds or \emph{catamorphisms}. In
the case of lists, this pattern has been captured in the well-known |foldr|
function.
\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []        = z
foldr f z (x : xs)  = f x (foldr f z xs)
\end{code}
Indeed, the research literature is full of applications,
properties and optimizations based on folds. \tom{add many citations}

Hence, given all these advantages of folds, one would expect every programmer
to diligently avoid explicit recursion where folds can do the job.
Unfortunately, that is far from true in practice. For many reasons, programmers
do not write their code in terms of explicit folds. This class comprises a
large set of advanced functional programmers \tom{evidence of our case study}.
This is compounded by the fact that programmers often do not bother to define
the equivalent of |foldr| for other inductive algebraic datatypes.

Yet, sadly, these first-order recursive functions are treated as second-class
by compilers. They do not benefit from the same performance gains like loop
fusion and deforestations. In fact, the leading Haskell compiler GHC won't even
inline recursive functions. We disagree with this injustice and argue that it
is quite unnecessary to penalize programmers for using first-class recursion.
In fact, we show that with a little effort, catamorphisms can be detected
automatically by the compiler and automatically transformed into explicit
invocations of folds for the purpose of automation.

In particular, our specific contribuations are:
\begin{enumerate}
\item We show how to automatically identify \emph{catamorphisms} and transform
      them into explicit calls to |fold|. 
\item In order to support a particular well-known optimization,
      fold-build fusion, we also show how to automatically detect and transform
      functions that can be expressed as a call to |build|.
\item We provide a GHC compiler plugin that performs these detections and
      transformations on GHC Core.
      It covers not only catamorphisms over Haskell lists, but catamorphisms
      over all inductively defined directly recursive datatypes.
\item We have performed a case study of our detection and transformation
      plugin on a range of well-known Haskell packages and applications
      to take stock of the number of explicitly recursive catamorphisms
      and currently missed opportunities for fold-build fusion.
      \tom{The results are astounding.}
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
\subsection{Folds, Builds and Fusion}

One of the main advantages of expressing functions in terms of fold is that
they inherit known properties of fold, which can be used for reasoning or for
\emph{optimization}.  In this work, we look at one such optimization and first
explain it for lists before generalizing it to other inductive datatypes.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Folds}
Catamorphisms are functions that \emph{consume} an inductively defined datastructure
by means of structural recursion.  Here are two examples of catamorphisms over
the most ubiquitous inductive datatype, lists.
\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs

sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs
\end{code}

Instead of using explicit recursion again and again, the catamorphic 
pattern can be captured once and for all in a higher-order
function, the fold function. In case of list, the fold function
is also known as |foldr|.
\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []        = z
foldr f z (x : xs)  = f x (foldr f z xs)
\end{code}

Any other catamorphism over lists can easily be expressed
as an invocation of |foldr|.

\begin{code}
upper' :: String -> String
upper' = foldr (\x xs -> toUpper x : xs) []

sum' :: [Int] -> Int
sum' = foldr (+) 0
\end{code}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Build}

The |build| function captures a particular pattern of list \emph{production}.
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
replicate' :: Int -> a -> [a]
replicate' n x = build $ \cons nil ->
    let g n' x'
            | n' <= 0    = nil
            | otherwise  = cons x' (g (n' - 1) x')
    in g n x
\end{code}
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Fusion}
The foldr/build fusion rule expresses that a consumer and producer can be fused:
\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]

Consider the following expressions:
\begin{spec}
sum' (replicate' n x)
\end{spec}
which 
consumes a list with |sum'| after generating it with |replicate'|. 
With the help of the fusion rule and simple transformations, we can optimize it
as follows.
\begin{spec}
    sum' (replicate' n x)

== {- inline |sum'| -}

    foldr (+) 0 (replicate' n x)

== {- inline |replicate'| -}

    foldr (+) 0 (build $ \cons nil ->
        let g n' x'
                | n' <= 0    = nil
                | otherwise  = cons x' (g (n' - 1) x')
        in g n x)

== {- foldr/build fusion -}

    (\cons nil ->
        let g n' x'
                | n' <= 0    = nil
                | otherwise  = cons x' (g (n' - 1) x')
        in g n x) (+) 0

== {- $\beta$-reduction -}

    let g n' x'
            | n' <= 0    = 0
            | otherwise  = x' + g (n' - 1) x'
    in g n x

\end{spec}
Although arguable less readable, we can see that the final version of |sum'
(replicate' n x)| does not need to create an intermediate list.

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

With the help of |foldr|/|build| fusion, whole pipelines like |sumOfSquareOdds| can be
fused into one recursive function:
\begin{code}
sumOfSquaredOdds :: Int -> Int
sumOfSquaredOdds n = go 1
  where
   go :: Int -> Int
   go x
     | x > n      = 0
     | odd x      = x ^ 3 + go (x+1)
     | otherwise  = go (x+1)
\end{code}
which performs only a single loop and allocates no intermediate lists. 

The key to pipeline optimization is the fact that transformation functions
like |map| and |filter| can be expressed as a |build| whose generator
function is a |foldr|.
\begin{spec}
map :: (a -> b) -> [a] -> [b]
map f l = build (\cons nil -> foldr (cons . f) nil l)

filter :: (a -> Bool) -> [a] -> [a]
filter p l = 
  build (\cons nil -> foldr (\x -> if p x  then cons x 
                                           else id) nil l)
\end{spec}
and |build|. This means they can fuse with both the producer before it and the
consumer after it.

Note that several specialized fusion laws in the literature, like
\begin{equation*}
  |map f . map g| | == | |map (f . g)| 
\end{equation*}
are merely a special case of the |foldr|/|build| law. 

% \noindent Let us briefly list the advantages these alternative versions exhibit.
% 
% \begin{itemize}
% 
% \item First, it is immediately clear to any functional programmer who has
% grasped the concepts of |map| and |foldr|, how these functions operate on their
% argument(s).
% 
% Once the higher-order function is understood in terms of performance,
% control flow, and other aspects, it is usually trivial to understand functions
% written in terms of this higher-order function. As such, the code can be grokked
% more swiftly and without suprises.
% 
% % TODO: Cite something on concise code can be read faster (some Scala study?)
% 
% \item Second, the code becomes much more concise. This results in less
% boilerplate, less code to read (and to debug). Since the number of bugs is
% usually proportional to the number of code lines \cite{gaffney1984}, this
% suggests there should be fewer bugs.
% 
% \item Third, famous higher-order functions exhibit well-known
% properties that allow them to be reasoned about. For example, for any |f| and
% |xs|:
% 
% \begin{spec}
% length (map f xs) == length xs
% \end{spec}
% 
% As such, these properties need only be proven once, independently of |f|. This
% approach saves quite some effort when reasoning about the program we are writing
% (or debugging).
% 
% In our example, we can immediately deduce that |upper'| does not change the
% length of its argument, because it is implemented in terms of |map|.
% 
% \item Finally, a number of well-known properties also allow for certain
% optimisations. Map fusion is a well-known example \cite{meijer1991}:
% 
% \begin{spec}
% map f . map g = map (f . g)
% \end{spec}
% 
% This optimisation merges two maps over a list, so that no temporary list needs
% to be created, and we only need to loop over a list once instead of twice.
% 
% \end{itemize}
% 
% Hence, it should be clear that manually rewriting functions using higher-order
% functions offers some nice advantages. In what follows, we will aim for
% automating this manual labour, further simplifying the programmer's task. In
% order to do so, we need some manner in which to detect recursion patterns in a
% (sufficiently) general way.


%-------------------------------------------------------------------------------
\subsection{Generalization}

% As we mentioned in the introduction, one of our goals is to automatically detect
% instances of well-known recursion patterns.  Our work around the detection of
% recursion pattern revolves mostly around |foldr|. There are several reasons for
% this.
% 
% First, |foldr| is an \emph{elementary} higher-order function. Many other
% higher-order functions (such as |map|, |filter|, and |foldl|) can actually be
% redefined in terms of |foldr|.
% 
% \begin{code}
% map' :: (a -> b) -> [a] -> [b]
% map' f = foldr (\x xs -> f x : xs) []
% \end{code}
% 
% This means that every function which can be written as an application of |map|
% can also be written as an application of |foldr|.
% 
% This allows us to work in a bottom-up fashion, first detecting a |foldr|-like
% pattern before classifying the pattern as an instance of a more specific
% higher-order function such as |map|.

While we have shown the above example on lists, the above ideas easily
generalize to other inductively defined algebraic datatypes.
We illustrate that on leaf trees.
\begin{code}
data Tree a
    = Leaf a
    | Branch (Tree a) (Tree a)
    deriving (Show)
\end{code}

\paragraph{Fold}
The |sumTree| function is an example of a directly recursive catamorphism
over leaf trees.
\begin{code}
sumTree :: Tree Int -> Int
sumTree (Leaf x)      = x
sumTree (Branch l r)  = sumTree l + sumTree r
\end{code}

However, the catamorphic recursion scheme over leaf
trees can be captured in a fold function
\begin{code}
foldTree  ::  (a -> r)
          ->  (r -> r -> r)
          ->  Tree a
          ->  r
foldTree l _ (Leaf x)      = l x
foldTree l b (Branch x y)  =
    b (foldTree l b x) (foldTree l b y)
\end{code}
which enables us to define |sumTree'| succinctly as
\begin{code}
sumTree' :: Tree Int -> Int
sumTree' = foldTree id (+)
\end{code}

In general, a fold function transforms an inductive datatype into a value of a
user-specified type |r| by replacing every constructor by a user-specified
function.

Note that the fold function for a datatype is unique up to isomorphism (e.g.,
swapping the order of arguments), and characterized by the \emph{universal property}
of folds~\cite{hutton1999}.  In fact, the fold function for an inductive
datatype can be derived automatically from its definition. We have implemented
a Template Haskell~\cite{sheard2002} routine, |deriveFold|, to do so. For example, 
%{
%format Tree = "`Tree"
\begin{spec}
$(deriveFold Tree "foldTree")
\end{spec}
%}

generates the fold function, named |foldTree|, for the type |Tree|.

\paragraph{Build}
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
range' :: Int -> Int -> Tree a
range' l u  = buildTree $ \leaf branch ->
  let g l u
    | u > l      =  let m = l + (u - l) `div` 2
                    in  branch (g l m) (g (m+1) u)
    | otherwise  =  leaf l
  in g l u
\end{code}

Just like for folds, we have automated the writing
of build functions with Template Haskell:

%{
%format Tree = "`Tree"
\begin{spec}
$(deriveBuild Tree "buildTree")
\end{spec}
%}
yields the build function, named |buildTree|, for the type |Tree|.

\paragraph{Fusion}
Any type that provides both a fold and build function, has a corresponding
fusion law. For leaf trees, this law is:
\[ |foldTree leaf branch (buildTree g)| ~~ |==| ~~ |g leaf branch| \]

It is key to fusing two loops into one:
\begin{spec}
    sumTree' (range' l u)

== {- inline |sumTree'| -}

    foldTree id (+) (range' l u)

== {- inline |range'| -}

    foldTree id (+) (buildTree $ \leaf branch ->
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

The main Haskell compiler, GHC, currently provides limited automation for
foldr/build fusion: by means of a GHC rewrite rule.  When functions are defined
explicitly in terms of |foldr| and |build|, after inlining, the rewrite rule
may perform the fusion.

Unfortunately, this existing automation is severely limited. Firstly, it is
restricted to lists and secondly it requires programmers to explicitly define
their functions in terms of |build| and |foldr|. The latter is further
compounded by the fact that |build| is a non-exported function of the
|Data.List| library.

This work lifts both limitations. It allows programmers to write their
functions in explicitly recursive style and performs foldr/build fusion for any
directly inductive datatype.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discovering Folds}
\label{subsection:identifying-folds}

This section explains our approach to turning explicitly recrusive
functions into invocations of |fold|.

%-------------------------------------------------------------------------------
\subsection{Syntax and Notation}
\label{section:core-expressions}

To simplify the presentation, we do not explain our approach in terms of
Haskell source syntax or even GHC's core syntax (based on System F). Instead, we use
the untyped lambda-calculus extended with constructors and pattern matching,
and (possibly recursive) bindings.  
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
|triangle|. The former is used for a sequence of unimportant arguments, while
the latter marks an argument of significance. The function
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
\subsection{Discovering Folds}
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
algebraic datatypes later on.\tom{Where?}

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
      function, is the function |suff|.
\begin{spec}
suff = \y -> case y of
              []      -> []
              (v:vs)  -> vs : suff vs
\end{spec}
This function can be written as 
\begin{spec}
suff = para (\v vs ws -> vs : ws) []
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
f = \x -> case y of
            []      -> 0
            (v:vs)  -> v + f vs + f [1,2,3]
\end{spec}
\end{enumerate}
Note that we know in the branches |e1| and |e2| the variable |x| is an alias
for respectively |[]| or |(y:ys)|. Rule (\textsc{F-Bind'}) exploits the former
case to eliminate |x| in |e'1|. The latter case reveals an improper
catamorphism, where |ys| appears outside of a recursive call (issue 2 above);
hence, rule \textsc{(F-Bind')} does not allow it.

\paragraph{Multi-Argument Functions}
Rule \textsc{(F-Bind)} generalizes rule \textsc{(F-Bind')} by supporting
additional arguments |many x| and |many z| before and after the scrutinee
argument |y|. We distinguish two kinds of additional arguments.
The first kind are arguments that are \emph{invariant} in the recursion. An
example of that is the |f| parameter in the |map| function.
\begin{spec}
map = \f y -> case y of
                []      -> []
                (v:vs)  -> (:) (f v) (map f vs)
\end{spec}
Rule \textsc{(F-Bind)} does not explicitly name these invariant arguments, but
captures them instead in the recursive call context |E|. For instance, for |map|
the context has the form |map f triangle|.

The second kind of additional arguments are \emph{variant} in the recursion.
Catamorphisms with an accumulating parameter are typical examples of these. E.g.,
\begin{spec}
sum' = \y acc -> case y of
                   []      -> acc
                   (v:vs)  -> sum' vs (v + acc)
\end{spec}
Rule \textsc({F-Bind)} names these variant arguments |many u| and leaves |box|
holes in the context |E| for them. For instance, the context of |sum'| is |sum'
triangle box|.  Because the |many u| arguments vary throughout the iteration,
their current and new values need to be bound, respectively supplied, at every
step. The binding of the current values is taken care of by the binders |\many
u ->| in the two first parameters of |foldr|. Also the initial values for |many
u| are supplied as extra parameters to |foldr|.

Rule \textsc{(F-Rec)} captures the new values |many e| for the variant
arguments with the help of the context |E|; a recursive call takes the form
$|E|[|many e|;|vs|]$. The rule passes these variant arguments explicitly to the
recursive result |ws|. For instance, after rewriting |sum'| we get
\begin{spec}
sum' = \y acc -> foldr  (\v ws acc -> ws (v + acc)) 
                        (\acc -> acc) y acc
\end{spec}
Note that rule \textsc{(F-Rec)} recursively rewrites the variant arguments
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
head' :: [a] -> a
head' = \l -> foldr (\z zs -> z) (error "empty list") l
\end{code}
These \emph{degenerate} folds are of no interest to us, since non-recursive functions
are much more easily understood as they are than as a fold. Moreover, they can
easily be optimized without 
fold/build fusion: by simple inlining and specialization. 
Fortunately we can easily avoid introducing degenerate folds by only rewriting
recursive functions. In other words, the algorithm must use 
the rule \textsc{(F-Rec)} at least once.
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discovering Builds}

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
discoverings list builds. The toplevel judgement is $b \rightarrowtail b';
b_g$.  It rewrites a binding |b| into |b'| that uses |build| and also returns
an auxiliary binding $b_g$ for the generator function used in the |build|.
There is one rule defining this judgement, (\textsc{B-Bind}), that rewrites
the body |e| of a binding into a |build| and produces the generator function binding.
Note that the rule allows for an arbitrary number of lambda abstractions |\many
x ->| to preceed the invocation of |build|. This enables auxiliary parameters to
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
      to |build|. It could have dynamically introduced the abstract |c| and |n| list constructors 
      by means of |foldr c n (build e)|. However, this expression can be statically fused to |e c n|.
\end{enumerate}
In the |map| example, all rules but (\textsc{B-Build}) of the rules are used.
Here is an example that does use rule (\textsc{B-Build}).
\begin{spec}
toFront :: Eq a => a -> [a] -> [a]
toFront x xs = x : filter (/= x) xs
\end{spec}
After inlining |filter|, this function becomes.
\begin{spec}
toFront = \x -> \xs -> x : build (g (/= x) xs)
\end{spec}
which can be transformed into:
\begin{spec}
toFront = \x -> \xs -> build (g' x xs)
g'  = \x -> \xs -> \c -> \n ->  c x (g' (/= x) xs c n)
\end{spec}
%-------------------------------------------------------------------------------
\subsection{Degenerate Builds}

Just like we called non-recursive catamorphisms, degenerate |folds|,
we can also call non-recursive builds degenerate.
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

Strictly speaking, such non-recursive functions do not require |foldr|/|build|
fusion to be optimized. They can also be optimized by inlining the 
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
Hence, |foldr|/|build| fusion is still a good way of getting rid of the
intermediate datastructure.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}

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
\subsection{Identifying folds}
\label{subsection:identifying-folds}

A first aspect we can evaluate is how well our detection of folds works.
Unfortunately, manually identifying folds in projects takes too much time. This
explains why it is especially hard to detect false negatives.

Additionally, very little other related work is done. The \emph{hlint}
\cite{hlint} tool is able to recognize folds as well, but its focus lies on
refactoring rather than optimisations.

In Table \ref{tabular:project-results}, we can see the results of running our
tool on some well-known Haskell projects. We classify folds into three
categories:

\begin{itemize}
\item Degenerate folds, as described in \ref{subsection:degenerate-folds};
\item List folds, folds over data structures of type |[a]|;
\item Data folds, folds over any other data structure.
\end{itemize}

\tom{We should omit degenerate folds from the table because they are not interesting.}

\begin{table}
\begin{center}
\ra{1.3}
\begin{tabular}{@@{}lrrrr@@{}}
\toprule
                    & Degenerate & List & Data & hlint \\
\midrule
\textbf{hlint}      &   248             & 17   & 25  & 0     \\
\textbf{parsec}     &   150             &  6   &  0  & 0     \\
\textbf{containers} &   311             &  7   & 75  & 0     \\
\textbf{pandoc}     & 1,012             & 35   &  1  & 0     \\
\textbf{cabal}      & 1,701             & 43   & 30  & 1     \\
\bottomrule
\end{tabular}
\caption{Results of identifying folds in some well-known projects}
\label{tabular:project-results}
\end{center}
\end{table}

We also tested our tool on the test cases included in the hlint source code, and
we identified the same folds. However, in arbitrary code (See Table
\ref{tabular:project-results}), our tool detects more possible folds than hlint.
This suggests that we detect a strict superset of possible folds, even for
lists. The fact that the number of possible folds in these projects found by
hlint is so low indicates that the authors of the respective packages might have
used hlint during development.

%-------------------------------------------------------------------------------
\subsection{Identifying builds}

%-------------------------------------------------------------------------------
\subsection{Optimization results}

\tom{We need to specifically address what happens to functions that are both
     a fold and a build like |map| and |filter|.}

\tom{We need to benchmark foldr/build examples from the literature.}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related work}

In ``A short cut to deforestation'' \cite{gill1993}, the foldr/build rule is
discussed. The authors discuss the benefits of this approach, supported by many
benchmarks. However, they also mention the issues with the fact that every
programmer needs to use a specific style (i.e., write all functions in terms of
|foldr|/|build|). Naturally, this is exactly what our research mitigates!

Stream fusion \cite{coutts2007} is an advanced alternative to foldr/build
fusion. It has the benefits of easily being able to fuse zips and left folds.
However, at the time of writing, there is no known reliable method of optimising
uses of |concatMap|. |concatMap| is important because it represents the entire
class of nested list computations, including list comprehensions
\cite{coutts2010}.

The \emph{hlint} \cite{hlint} tool is also able to recognise several
higher-order functions, under which |foldr|. However, as we already showed in
\ref{subsection:identifying-folds}, we are able to detect more instances of
folds for Haskell lists. Additionally, detecting fold instances for arbitrary
algebraic datatypes is outside of the scope of hlint.

\begin{itemize}
\item fold applications
\item supercompilation
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
