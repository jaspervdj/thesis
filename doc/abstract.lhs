\documentclass[twocolumn]{phdsymp} %!PN

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
%format elapsed = "\ldots"
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
\newcommand{\todo}[1]{\textcolor{red}{\textbf{[\textsc{TODO:} \textcolor{black}{#1}]}}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Ugly fixes to the awful ugent template
\renewcommand{\mathit}[1]{{#1}}
\def\newblock{\hskip .11em plus .33em minus .07em}
\renewcommand{\paragraph}[1]{\noindent\textit{\textsc{#1.}}~}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Automatic Detection of Recursion Patterns}
\author{Jasper Van der Jeugt}
\supervisor{prof dr. ir. Tom Schrijvers, Steven Keuchel}

\begin{document}

\maketitle

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types      #-}
import Data.Char     (toUpper)
import Prelude       hiding (head, foldr, map, sum, replicate)

elapsed :: a
elapsed = undefined
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

\begin{keywords}
catamorphisms, fold-build fusion, analysis, transformation
\end{keywords}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

Higher-order functions are immensely popular in Haskell, whose Prelude alone
offers a wide range of them (e.g., |map|, |filter|, |any|, \ldots). This is
not surprising, because they are the key \emph{abstraction} mechanism of
functional programming languages. They enable capturing and reusing common
patterns among, often recursive, function definitions to a much larger extent
than first-order functions. In addition to the obvious code reuse and
increased programmer productivity, uses of higher-order functions have many
other potential advantages over conventional first-order definitions.

\begin{itemize}

\item Uses of higher-order functions can be more quickly understood because
they reduce the that is already known pattern to a single name and thus draw
the attention immediately to what is new (i.e., the function parameters).

\item Because the code is more compact and the number of bugs is proportional
to code size~\cite{gaffney1984}, higher-order functions should lead to fewer
bugs.

\item Properties can be established for the higher-order function independently
from its particular uses. This makes (e.g., equational) reasoning more
productive.

\item Since properties and occurrences are more readily available, they make
good targets for automatic optimisation in compilers.

\end{itemize}

A particularly ubiquitous pattern is that of folds or \emph{catamorphisms}. In
the case of lists, this pattern has been captured in the well-known |foldr|
function.

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []        = z
foldr f z (x : xs)  = f x (foldr f z xs)
\end{code}

Indeed, the research literature is full of applications, properties and
optimisations based on folds \cite{wadler1990, gill1993, meijer1991,
hutton1999}.

Hence, given all these advantages of folds, one would expect every programmer to
diligently avoid explicit recursion where folds can do the job.  Unfortunately,
that is far from true in practice. For many reasons, programmers do not write
their code in terms of explicit folds. This class comprises a large set of
advanced functional programmers (see \ref{subsection:identifying-folds}). This
is compounded by the fact that programmers often do not bother to define the
equivalent of |foldr| for other inductive algebraic datatypes.

Yet, sadly, these first-order recursive functions are treated as second-class
by compilers. They do not benefit from the same performance gains like loop
fusion and deforestation. In fact, the leading Haskell compiler GHC won't
even inline recursive functions.

We disagree with this injustice and argue that it is quite unnecessary to
penalize programmers for using first-class recursion. In fact, we show that
with a little effort, catamorphisms can be detected automatically by the
compiler and automatically transformed into explicit invocations of folds for
the purpose of automation.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Folds, Builds and Fusion over Lists}

Catamorphisms are functions that \emph{consume} an inductively defined
datastructure by means of structural recursion. They can be expressed in terms
of |foldr| \cite{meijer1991}.

The |build| function is the dual to the |foldr| function. Where the |foldr|
function captures a pattern of list \emph{consummation}, |build| captures a
particular pattern of list \emph{production}.

%format . = "."
\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}
%}

Given these functions, we can \emph{fuse} the production and consummation of a
list: meaning that no intermediate datastructure needs to be allocated. The
foldr/build-fusion rule is given by:

\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]

The main Haskell compiler, GHC, currently provides limited automation for
foldr/build-fusion: by means of a GHC rewrite rule.  When functions are
defined explicitly in terms of |foldr| and |build|, after inlining, the
rewrite rule may perform the fusion.

Unfortunately, this existing automation is severely limited. Firstly, it is
restricted to lists and secondly it requires programmers to explicitly define
their functions in terms of |build| and |foldr|.

This work lifts both limitations. It allows programmers to write their
functions in explicitly recursive style and performs foldr/build-fusion for
any directly inductive datastructure.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discovering Folds and Builds}
\label{subsection:identifying-folds-and-builds}

We have devised a set of formal rewrite rules to turn explicitly recursive
functions into folds and to rewrite producers into builds where possible.

\subsection{Syntax and Notation}
\label{section:core-expressions}

To simplify the presentation, we do not use Haskell source syntax or even
GHC's core syntax (based on System F). Instead, we use the untyped
lambda-calculus extended with constructors and pattern matching, and (possibly
recursive) bindings.

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

The extension to GHC's full core syntax, including types, is relatively
straightforward. We also need an advanced form of \emph{(expression) context}:

\[\begin{array}{lcl}
|E| & ::=  & |x| \\
    & \mid & |E x| \\
    & \mid & |E box| \\
    & \mid & |E triangle|
\end{array}\]

A context |E| denotes a function applied to a number of arguments. The
function itself and some of its arguments are given (as variables), while
there are holes for the other arguments. In fact, there are two kinds of
holes: boxes |box| and triangles |triangle|. The former is used for a sequence
of unimportant arguments, while the latter marks an argument of significance.

The function $|E|[|many e|;e]$ turns a context |E| into an expression by
filling in the holes with the given expressions.

\[\begin{array}{lcl}
|x|[\epsilon;|e|]                   & =  & |x| \\
(|E x|)[|many e|;|e|]         & =  & |E|[|many e|;|e|]\, |x| \\
(|E box|)[|many e|,|e1|;|e|]  & =  & |E|[|many e|;|e|]\, |e1| \\
(|E triangle|)[|many e|;|e|]  & =  & |E|[|many e|;|e|]\, |e| \\
\end{array}\]

Note that this function is partial; it is undefined if the number of
expressions |many e| does not match the number of box holes.

\subsection{Rules}

The non-deterministic rules to rewrite functions into folds or builds can be
found in Figure \ref{fig:foldspec} and Figure \ref{fig:buildspec} respectively.
To keep the exposition simple, they are only given for lists and not arbitrary
algebraic datastructures: the specifics for this generalization can be found in
the full text. As an illustration, consider |map|, which is both a fold as well
as a build.

\begin{code}
map = \f y -> case y of
    []      -> []
    (v:vs)  -> f v : map f vs
\end{code}

Applying the rules for build detection yields us:

\begin{code}
map  = \f -> \l -> build (g f l)
g    = \f -> \l -> \c -> \n ->
        case l of
          []      -> n
          (y:ys)  -> c (f y) (g f ys c n)
\end{code}

Now |g| can be recognise by our fold detection rules:

\begin{code}
g   = \f -> \l -> \c -> \n ->
        foldr (\y ys -> c (f y) ys) n l
\end{code}

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

\begin{figure}[b]
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}

We implemented these transformations on top of GHC \cite{ghc}, the de-facto
standard compiler for Haskell. Since GHC 7.2.1, a plugin framework is available
\cite{ghc-plugins}.

This plugin framework facilitates writing GHC Core \cite{tolmach2009}
transformations. Using this framework, we no longer have to edit the GHC source
code in order to add, modify or delete Core-to-Core passes: we can do so in a
plugin. This plugin is then passed to GHC using a command-line argument.

We implemented such a plugin, which contains passes:

\begin{itemize}

\item A pass to convert functions written in explicitly recursive style into
functions in terms of folds. This pass is a deterministic implementation of the
rules in Figure \ref{fig:foldspec}. Directly inductive datastructures other than
list are also supported.

\item We have a similar pass for builds: a deterministic implementation of the
rules in Figure \ref{fig:buildspec}.

\item A custom inliner, over which we have a bit more control than the default
GHC inliner. However, we ultimately decided not to use this custom inliner, so
it is disabled by default.

\item An implementation of foldr/build-fusion for any algebraic datatype for
which we have a fold and a build. By using this pass, we can avoid having to add
extra rule pragmas \cite{jones2001}.

\end{itemize}

Additionally our work also contains Template Haskell \cite{sheard2002} routines
to mitigate the burden of defining folds and builds for algebraic datatypes.
These folds and builds can be generated by issuing, e.g., for a type |Tree|:

%{
%format Tree = "`Tree"
\begin{spec}
$(deriveFold Tree "foldTree")
$(deriveBuild Tree "buildTree")
\end{spec}
%}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}

\subsection{Identifying folds}
\label{subsection:identifying-folds}

A first aspect we can evaluate is how well our detection of folds works.
Unfortunately, manually identifying folds in projects very labour-intensive.
This explains why it is especially hard to detect false negatives.

Additionally, very little other related work is done. There is the \emph{HLint}
\cite{hlint} tool is able to recognize folds as well, but its focus lies on
refactoring rather than optimisations. We cannot directly compare our results
with those of HLint since we detect folds over all possible directly inductive
datastructures, and HLint is limited to list. Hence, we classify the folds we
detect as either a fold over a list or a fold over some other datastructure.

Table \ref{tabular:fold-detection-results} shows that we clearly detect more
folds than the HLint tool does. Additionally, we also tried our tool on the test
cases included with HLint -- which we could all correctly detect. This suggests
that we detect a strict superset of possible folds, even for lists. The fact
that the number of possible folds in these projects found by HLint is so low
indicates that the authors of the respective packages might have used HLint
during development.

\begin{table}
\begin{center}
{\renewcommand{\arraystretch}{1.20} % Slightly more spacing
\begin{tabular}{lrrrr}
                          & Total & List & ADT & HLint \\
\textbf{Cabal}            & 20    & 11   & 9   & 9     \\
\textbf{containers}       & 100   & 11   & 89  & 1     \\
\textbf{cpphs}            & 5     & 2    & 3   & 1     \\
\textbf{darcs}            & 66    & 65   & 8   & 6     \\
\textbf{ghc}              & 327   & 216  & 111 & 26    \\
\textbf{hakyll}           & 5     & 1    & 4   & 0     \\
\textbf{haskell-src-exts} & 37    & 11   & 26  & 2     \\
\textbf{hlint}            & 6     & 3    & 3   & 0     \\
\textbf{hscolour}         & 4     & 4    & 0   & 2     \\
\textbf{HTTP}             & 6     & 6    & 0   & 3     \\
\textbf{pandoc}           & 15    & 15   & 0   & 2     \\
\textbf{parsec}           & 3     & 3    & 0   & 0     \\
\textbf{snap-core}        & 4     & 3    & 1   & 0     \\
\end{tabular}
}
\caption{Results of identifying folds in some well-known projects}
\label{tabular:fold-detection-results}
\end{center}
\end{table}

\subsection{Identifying builds}

We also evaluated the detection of builds. However, as far as we know no work
has been done in this area -- hence, we cannot compare these results to anything
meaningful. The results are shown in Table
\ref{tabular:build-detection-results}.  We conclude that they are within the
same order of magnitude as the number of folds we found.

\begin{table}
\begin{center}
{\renewcommand{\arraystretch}{1.20} % Slightly more spacing
\begin{tabular}{lrrr}
                          & Total & List & ADT \\
\textbf{Cabal}            & 101   & 81   & 20  \\
\textbf{containers}       & 25    & 2    & 23  \\
\textbf{cpphs}            & 6     & 5    & 1   \\
\textbf{darcs}            & 354   & 354  & 0   \\
\textbf{ghc}              & 480   & 178  & 302 \\
\textbf{hakyll}           & 22    & 18   & 4   \\
\textbf{haskell-src-exts} & 140   & 74   & 66  \\
\textbf{hlint}            & 69    & 62   & 7   \\
\textbf{hscolour}         & 33    & 33   & 0   \\
\textbf{HTTP}             & 11    & 11   & 0   \\
\textbf{pandoc}           & 97    & 97   & 0   \\
\textbf{parsec}           & 10    & 10   & 0   \\
\textbf{snap-core}        & 4     & 4    & 0   \\
\end{tabular}
}
\caption{Results of identifying builds in some well-known projects}
\label{tabular:build-detection-results}
\end{center}
\end{table}

\subsection{Foldr/build-fusion}

Unfortunately it remains a hard problem to count how many times
foldr/build-fusion can be applied in a Haskell package. The concrete
difficulties we currently face are:

\begin{itemize}

\item Manual intervention is not required to do the detection of folds or
builds, but in order to actually perform the transformation some manual changes
are required: more precisely: adding imports and language pragmas, and using
Template Haskell to derive the necessary folds.

\item Code which is crucial to the performance of a package is often manually
optimised. Hence, we usually find no opportunities to remove intermediate
datastructures there.

\item A lot of code is partially written using higher-order functions (e.g. from
the |Data.List| library) and partially using explicit recursion. Due to
practical problems, we currently cannot perform any fusion there, although we
are working to lift this limitation.

\end{itemize}

\subsection{Benchmarks}

We researched the speedups caused by foldr/build-fusion. In order to do this, we
constructed small pipeline-like programs who have the inherent property of being
fusable. Consider the functions:

\begin{code}
sumt :: Tree Int -> Int
sumt (Leaf x)      = x
sumt (Branch l r)  = sumt l + sumt r

mapt :: (a -> b) -> Tree a -> Tree b
mapt f (Leaf x)      = Leaf (f x)
mapt f (Branch l r)  = Branch (mapt f l) (mapt f r)

uptot :: Int -> Int -> Tree Int
uptot lo hi
    | lo >= hi   = Leaf lo
    | otherwise  =
        Branch (uptot lo mid) (uptot (mid + 1) hi)
  where
    mid = (lo + hi) `div` 2
\end{code}

These auxiliary functions allow us to write functions which must allocate
intermediate datastructures, as the result of |uptot| and |mapt|. Hence, we can
benchmark the functions:

\begin{code}
t1, t2, t3, t4, t5 :: Int -> Int
t1 n = sumt (1 `uptot` n)
t2 n = sumt (mapt (+ 1) (1 `uptot` n))
t3 n = sumt (mapt (+ 1) (mapt (+ 1) (1 `uptot` n)))
t4 n = elapsed
t5 n = elapsed
\end{code}

The results can be found in Figure \ref{figure:benchmarks}. We can see that the
speedups are very significant, even when fusion can only be applied once (i.e.,
in |t1|). We also see that the more we can apply foldr/build-fusion, the more
significant our speedup becomes.

\begin{figure}[h]
\includegraphics[width=\columnwidth]{plots/tree-en.pdf}
\caption{Benchmarking the specified functions with and without fusion}
\label{figure:benchmarks}
\end{figure}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

\subsection{Applications of Folds and Fusion}

There is a long line of work on writing recursive functions in terms of
structured recursion schemes, as well as proving fusion properties of these and
exploiting them for deriving efficient programs.

Bird and Meertens~\cite{bird,meertens} have come up with several equational
laws for recursion schemes to serve them in their work on program calculation.

With their Squiggol calculus, Meijer et al.~\cite{meijer1991} promote the use
of structured recursion by means of recursion operators. These operators are
defined in a datatype generic way and are equipped with a number of algebraic
laws that enable equivalence-preserving program transformations.

Gibbons~\cite{Gibbons2003:Origami} promotes explicit programming in terms of
folds and unfolds, which he calls \emph{origami} programming. Unfolds are the dual
of folds, and capture a special case of builds.

Gill et al.~\cite{gill1993} present the foldr/build-fusion rule and discuss
its benefits. They mention that it would be desirable, yet highly challenging,
for the compiler to notice whether functions can be expressed in terms of |foldr|
and |build|. That would allow programmers to write programs in whatever style they like.

Stream fusion~\cite{coutts2007} is an alternative to foldr/build-fusion. It
has the benefits of easily being able to fuse zips and left folds. However, at
the time of writing, there is no known reliable method of optimising uses of
|concatMap|. |concatMap| is important because it represents the entire class of
nested list computations, including list comprehensions~\cite{coutts2010}.

\subsection{Automatic Discovery}

The \emph{HLint}~\cite{hlint} tool is designed to recognize various code
patterns and offer suggestions for improving them. In particular, it recognizes
various forms of explicit recursion and suggests the use of appropriate
higher-order functions like |map|, |filter| and |foldr| that capture these
recursion patterns. As we already showed in Section
\ref{subsection:identifying-folds}, we are able to detect more instances of
folds for Haskell lists than HLint. Moreover, HLint makes no effort to detect
folds for other algebraic datatypes.

Sittampalam and de Moor~\cite{mag} present a semi-automatic approach to |foldr|
fusion based on the MAG system. In their approach, the programmer specifies the
initial program, a specification of the target program and suitable rewrite
rules. Then the MAG system will attempt to derive the target implementation by
applying the rewrite rules.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusions}

Programmers prefer high-level programming languages in order to be able to write
elegant, maintainable code. However, performance remains important, i.e.  the
code needs to be able to be translated to efficient assembly. The conflict
between those two goals can be solved fairly well by using advanced compilers
and smart optimisations.

We added such a smart optimisation. It allows the programmer to write small,
composable functions, either explicitly recursive or using a higher-order fold.
More complex functions van be expressed as a combination of these small building
blocks. When compiled naively, this would impose penalties on the performance,
because of the overhead of allocating, building and destroying intermediate
datastructures. By using foldr/build-fusion, we can avoid this overhead.

Our thesis has lifted the limitation that functions have to be written in a
certain style in order to benefit from foldr/build-fusion, and extends it to
work on any directly inductive datastructure instead of just lists.

\paragraph{Future work} A number of routes are still open for exploration. In
particular, we mention mutually recursive functions, mutually recursive
datatypes and GADTs \cite{cheney2003}. Folds and builds exists for these types
\cite{yakushev2009, johann2008}, but our detection rules are incapable of
finding these.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \appendix
% \section{Appendix Title}
% 
% This is the text of the appendix, if you need one.
% 
% \acks
% 
% Acknowledgments, if needed.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% References
\bibliographystyle{phdsymp}
\bibliography{references}

\end{document}
