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

\item Properties can be established for the higher-order function indepently
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
optimisations based on folds. \tom{add many citations}

Hence, given all these advantages of folds, one would expect every programmer
to diligently avoid explicit recursion where folds can do the job.
Unfortunately, that is far from true in practice. For many reasons, programmers
do not write their code in terms of explicit folds. This class comprises a
large set of advanced functional programmers \tom{evidence of our case study}.
This is compounded by the fact that programmers often do not bother to define
the equivalent of |foldr| for other inductive algebraic datatypes.

Yet, sadly, these first-order recursive functions are treated as second-class
by compilers. They do not benefit from the same performance gains like loop
fusion and deforestations. In fact, the leading Haskell compiler GHC won't
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
of |foldr| \todo{cite}.

The |build| function is the dual to the |foldr| function. Where the |foldr|
function captures a pattern of list \emph{consumation}, |build| captures a
particular pattern of list \emph{production}.

%format . = "."
\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}
%}

Given these functions, we can \emph{fuse} the production and consumation of a
list: meaning that no intermediate datastructure needs to be allocated. The
foldr/build-fusion rule is given by:

\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]

The main Haskell compiler, GHC, currently provides limited automation for
foldr/build fusion: by means of a GHC rewrite rule.  When functions are
defined explicitly in terms of |foldr| and |build|, after inlining, the
rewrite rule may perform the fusion.

Unfortunately, this existing automation is severely limited. Firstly, it is
restricted to lists and secondly it requires programmers to explicitly define
their functions in terms of |build| and |foldr|.

This work lifts both limitations. It allows programmers to write their
functions in explicitly recursive style and performs foldr/build fusion for
any directly inductive datatype.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discovering Folds and Builds}
\label{subsection:identifying-folds-and-builds}

We have divised a set of formal rewrite rules to turn explicitly recursive
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
found in Figure \ref{fig:foldspec} and Figure \ref{fig:buildspec}
respectively. To keep the exposition simple, they are only given for lists and
not arbitrary algebraic datatypes: the specifics for this generalization can
be found in the full text. As an illustation, consider |map|, which is both a
fold as well as a build.

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

%-------------------------------------------------------------------------------
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

Gill et al.~\cite{gill1993} present the foldr/build fusion rule and discuss
its benefits. They mention that it would be desirable, yet highly challenging,
for the compiler to notice whether functions can be expressed in terms of |foldr|
and |build|. That would allow programmers to write programs in whatever style they like.

Stream fusion~\cite{coutts2007} is an alternative to foldr/build fusion. It
has the benefits of easily being able to fuse zips and left folds. However, at
the time of writing, there is no known reliable method of optimising uses of
|concatMap|. |concatMap| is important because it represents the entire class of
nested list computations, including list comprehensions~\cite{coutts2010}.

%-------------------------------------------------------------------------------
\subsection{Automatic Discovery}
The \emph{hlint}~\cite{hlint} tool is designed to recognize various code
patterns and offer suggestions for improving them. In particular, it recognizes
various forms of explicit recursion and suggests the use of appropriate
higher-order functions like |map|, |filter| and |foldr| that capture these
recursion patterns.  As we already showed in Section
\ref{subsection:identifying-folds}, we are able to detect more instances of
folds for Haskell lists than hlint. Moreover, hlint makes no effort to detect
folds for other algebraic datatypes.

Sittampalam and de Moor~\cite{mag} present a semi-automatic approach to |foldr|
fusion based on the MAG system. In their approach, the programmer specifies the
initial program, a specficiation of the target program and suitable rewrite
rules. The latter includes a rule for |foldr| fusion: 
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% References
\bibliographystyle{phdsymp}
\bibliography{references}

\end{document}
