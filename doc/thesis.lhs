%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\documentclass[12pt]{report}

\usepackage[dutch]{babel}
\usepackage[font=it]{caption}
\usepackage[left=1.90cm, right=1.90cm, top=1.90cm, bottom=3.67cm]{geometry}
\usepackage[numbers]{natbib}  % For URLs in bibliography
\usepackage[xetex]{graphicx}
\usepackage{fontspec,xunicode}
\usepackage{enumitem}
\usepackage{listings}
\usepackage{titlesec}
\usepackage{url}

\newcommand{\TODO}[1]{\textbf{(TODO: #1)}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types      #-}
import Data.Char (toUpper)
import Prelude   hiding (filter, foldr, head, id, map, sum, product, replicate)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Style
% \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
\setmainfont{DejaVu Serif}
\setmonofont{Inconsolata}
\newfontfamily{\futura}[Scale=1.30]{Futura Std}

\newcommand{\chapterstyle}{\futura\huge}
\titleformat{\chapter}
  {\chapterstyle}  % format
  {\thechapter ~}  % label
  {0.00cm}         % sep
  {}               % before
  [\normalfont]    % after

\newcommand{\sectionstyle}{\futura\large}
\titleformat{\section}
  {\sectionstyle}
  {\thesection ~}
  {0.00cm}
  {}
  [\normalfont]

\newcommand{\subsectionstyle}{\futura}
\titleformat{\subsection}
  {\subsectionstyle}
  {\thesubsection ~}
  {0.00cm}
  {}
  [\normalfont]

\setlength{\parindent}{0.00cm}
\setlength{\parskip}{0.50cm}

\lstset{basicstyle=\ttfamily, keywordstyle=\ttfamily\bf}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{\futura\Huge Automatische detectie van recursiepatronen}
\author{Jasper Van der Jeugt}

\begin{document}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle
\tableofcontents


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Inleiding}

Laten we beginnen in het begin. Sinds er programmeertalen gebruikt worden, maakt
men gebruik van \emph{controlestructuren}. Deze laten toe de manier waarop het
programma wordt uitgevoerd te be\"invloeden. In assembleertaal zijn dit de
verschillende \emph{jump} instructies (\texttt{jmp}, \texttt{je}...).

Latere programmeertalen (bv. C), die op hoger niveau werken, voegden
controlestructuren van hoger niveau toe, zoals bijvoorbeeld \texttt{for}- en
\texttt{while}-lussen. Deze programmeertalen lieten echter meestal wel nog toe
om \emph{arbitraire} jumps te maken door middel van de \texttt{goto} instructie.
Dit wordt ge\"illustreerd in Figuur \ref{figure:for-vs-goto}.

\begin{figure}[h]
  \begin{minipage}[c]{0.5\textwidth}
    \begin{lstlisting}[language=C, gobble=4]
    int sum_squares_for(int n) {
      int i, sum = 0;

      for(i = 1; i <= n; i++) {
        sum += i * i;
      }

      return sum;
    }
    \end{lstlisting}
  \end{minipage}
  \begin{minipage}[c]{0.5\textwidth}
    \begin{lstlisting}[language=C, gobble=4]
    int sum_squares_goto(int n) {
      int i, sum = 0;

      i = 1;
      start: sum += i * i;
      i++;
      if(i <= n) goto start;

      return sum;
    }
    \end{lstlisting}
  \end{minipage}
  \caption{Twee semantisch equivalente programma's, \'e\'en met hoger-niveau
  controlestructuren en \'e\'en met \texttt{goto}'s}
  \label{figure:for-vs-goto}
\end{figure}

De versie die gebruikt maakt van \texttt{for} is eenvoudiger leesbaar voor
programmeurs die bekend zijn met dit concept. Ook is het mogelijk eigenschappen
uit te drukken over programmas die geschreven zijn in deze stijl, bijvoorbeeld
met Floyd-Hoare logica \cite{floyd1967}. Dit leidde zelfs tot de conclusie dat
het gebruik van \texttt{goto} volledig vermeden moet worden \cite{dijkstra1968}.

Een soortgelijke redenering is te maken over \emph{functionele
programmeertalen}. Deze talen maken geen gebruik van \texttt{goto} instructies,
maar implementeren controlestructuren door middel van \emph{recursie}.

Deze programmeertalen bieden een hoog niveau van abstractie, en moedigen de
programmeurs aan om gebruik te maken van \emph{higher-order} functies (bv.
|map|, |filter|, |any|, \ldots). Op deze manier is geen expliciete recursie
nodig. Dit biedt verschillende voordelen:

\begin{itemize}[topsep=0.00cm]
\item Voor een programmeur die bekend is met de gebruikte higher-order functies
is mogelijk de code veel sneller te begrijpen: ze herkennen onmiddelijk het
patroon dat aangeboden wordt door de functie en dienen enkel de argumenten van
deze functie te bestuderen.

\item Door gebruik te maken van higher-order functies wordt de code beknopter.
Eerder is aangetoond dat het aantal fouten in code proportioneel is tot de
grootte van de codebase \cite{gaffney1984}. Hieruit kunnen we concluderen dat
het gebruik van higher-order functies het aantal fouten in programmas zou moeten
reduceren.

\item Het is mogelijk eigenschappen \'e\'enmaal te bewijzen over een
higher-order functie voor willekeurige argumenten. Dit spaart ons werk uit als
we willen redeneren over code, want de resultaten van deze bewijzen gelden dan
voor elke applicatie van deze higher-order functie.

\item Ook de compiler kan gebruik maken van deze eigenschappen, om verschillende
optimalisaties uit te voeren op de code.
\end{itemize}

Er zijn dus weinig redenen om in deze talen expliciete recursie te gebruiken
wanneer een higher-order functie beschikbaar is. Toch blijkt dat veel
programmeurs nog gebruik maken van expliciete recursie.

Enkele redenen hiervoor zijn bijvoorbeeld dat de programmeur niet bekend is met
de higher-order functie, of dat er geen tijd is om de functie te refactoren. We
zien zelfs dat we voorbeelden terugvinden van expliciete recursie in code
geschreven door geavanceerde gebruikers van functionele programmeertalen
\TODO{cite: GHC HQ does it}.

De voordelen die hierboven beschreven staan vormen een motivatie om te
onderzoeken of het niet mogelijk is om deze functies, geschreven in expliciet
recursieve stijl, automatisch om te zetten in functies die gebruik maken van de
higher-order hulpfuncties. Op die manier kan de programmeur code schrijven in om
het even welke stijl, en toch genieten van de verschillende optimalisaties.

In dit document beschrijven we een aanpak om dit mogelijk te maken.

\TODO{Kort overzicht van de verschillende hoofdstukken}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

We kozen voor de functionele programmeertaal Haskell \cite{jones2003} omwille
van verschillende redenen:

\begin{itemize}[topsep=0.00cm]

\item Een grote variatie higher-order functies is beschikbaar in het Prelude en
in de aanvullende libraries.

\item Haskell is een sterk getypeerde programmeertaal. Deze types geven ons meer
informatie die we kunnen gebruiken in de transformaties.

\item De de-facto standaard Haskell Compiler, GHC \cite{ghc}, laat via een
plugin-systeem toe om code te manipuleren op een relatief eenvoudige manier
\TODO{Cite het deel over GHC plugins/implementatie...}.

\end{itemize}

In dit hoofdstuk geven we een kort overzicht van Haskell, en de relevante
higher-order functies voor dit werk.

\section{Haskell: types en functies}

Haskell is ontstaan uit de lambda-calculus. Het is dan ook logisch om hieruit te
vertrekken.

\begin{spec}
e ::= x        -- Een variabele
   |  e e      -- Functie-applicatie (links-associatief)
   |  \x -> x  -- Functie-abstractie (rechts-associatief)
\end{spec}

Dit is natuurlijk een zeer beperkte syntax en Haskell breidt deze sterk uit.
Beschouw bijvoorbeeld de volgende Haskell-functie en het lambda-calculus
equivalent:

\begin{minipage}{0.5\textwidth}
\begin{code}
middle x y = (x + y) / 2
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{spec}
middle = \x -> \y -> (/) ((+) x y) 2
\end{spec}
\end{minipage}

In tegenstelling tot de lambda-calculus \TODO{Cite lambda-calculus?}, is Haskell
ook een \emph{sterk getypeerde} programmeertaal. Functies worden, naast een
definitie, ook voorzien van een \emph{type-signatuur}:

\begin{code}
middle :: Float -> Float -> Float
\end{code}

Net zoals lambda-abstracties is de |->| in type-signaturen rechts-associatief.
Deze type-signatuur is dus equivalent met |Float -> (Float -> Float)|. Dit
concept heet \emph{currying}: we kunnen |middle| beschouwen als een functie die
twee |Float|-argumenten neemt en een |Float| als resultaatwaarde heeft, of als
een functie die \'e\'en Float argument neemt en functie van het type |Float ->
Float| als resultaatwaarde heeft.

In tegenstelling tot de lambda-calculus is het is Haskell niet nodig om gebruik
te maken van fixpoint-combinators: men kan eenvoudig expliciet recursieve
definities geven.

\begin{code}
fib :: Int -> Int
fib n = if n <= 1 then 1 else fib (n - 1) + fib (n - 2)
\end{code}

Verder breidt Haskell de lambda-calculus uit met \emph{algebra\"ische datatypes}
en \emph{pattern matching}.

Bijschouw bijvoorbeeld een datatype dat de exit-code van een programma
voorsteld:

\begin{code}
data ExitCode
    =  ExitSuccess
    |  ExitError Int
\end{code}

Met behulp van pattern-matching kan de onderliggende constructor onderzocht
worden:

\begin{code}
isError :: ExitCode -> Bool
isError (ExitError _)  = True
isError ExitSuccess    = False
\end{code}

Het typesysteem van Haskell is zeer complex en valt buiten de scope van dit
werk. Een interessante feature die we wel nodig hebben is
\emph{type-polymorfisme}. Beschouw bijvoorbeeld de polymorfe functie |id|, de
identiteitsfunctie:

\begin{code}
id :: a -> a
id x = x
\end{code}

Polymorfe datatypes zijn ook mogelijk. Een voorbeeld hiervan is de lijst.

\begin{spec}
data [a]
    =  a : [a]
    |  []
\end{spec}

Lijsten zijn alomtegenwoordig in functionele programmas en verdienen speciale
aandacht. Zo worden bijvoorbeeld |String|s in Haskell ook voorgesteld als
karakter-lijsten:

\begin{spec}
type String = [Char]
\end{spec}

Omdat een lijst een recursief datatype is, is het zeer gebruikelijk om
recursieve functies over lijsten te schrijven. Met behulp van de
standaard-functie |toUpper :: Char -> Char| kan men bijvoorbeeld een functie
schrijven die een volledige |String| omzet naar drukletters:

\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs
\end{code}

\section{Higher-order functies}

Omdat recursieve functies over lijsten zo veel voorkomen, kunnen we vaak
patronen onderscheiden.

\begin{code}
sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs

product :: [Int] -> Int
product []        = 1
product (x : xs)  = x * product xs
\end{code}

Deze patronen kunnen ge\"implementeerd worden door middel van higher-order
functies: functies die andere functies als parameters nemen. De twee
bovenstaande functies zijn bijvoorbeeld eenvoudige voorbeelden van het
|foldr|-patroon.

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _  z []        = z
foldr f  z (x : xs)  = f x (foldr f z xs)
\end{code}

Als we |sum| en |product| herschrijven met behulp van |foldr|, krijgen we veel
beknoptere definities:

\begin{code}
sum' :: [Int] -> Int
sum' = foldr (+) 0

product' :: [Int] -> Int
product' = foldr (*) 1
\end{code}

Andere voorbeelden van higher-order functies zijn |map| en |filter|. |map| laat
ons toe een functie uit te voeren op elk element van een lijst:

\begin{code}
map :: (a -> b) -> [a] -> [b]
map f = foldr (\x xs -> f x : xs) []

upper' :: String -> String
upper' = map toUpper
\end{code}

En |filter| wordt gebruikt om bepaalde elementen uit een lijst te selecteren:

\begin{code}
filter :: (a -> Bool) -> [a] -> [a]
filter f = foldr (\x xs -> if f x then x : xs else xs) []

odds :: [Int] -> [Int]
odds = filter odd
\end{code}

\section{De universele eigenschap van fold}

Het feit dat we zowel |map| als |filter| schrijven met behulp van |foldr| duidt
aan dat |foldr| een zeer interessante functie is. Meer bepaald, de universele
eigenschap van fold \cite{hutton1999} is als volgt:

\begin{minipage}[c]{0.3\textwidth}
\begin{spec}
g []        = v
g (x : xs)  = f x (g xs)
\end{spec}
\end{minipage}
\begin{minipage}[c]{0.3\textwidth}
\center{$\Leftrightarrow$}
\end{minipage}
\begin{minipage}[c]{0.3\textwidth}
\begin{spec}
g = foldr f v
\end{spec}
\end{minipage}

Concreet wil dat zeggen dat |foldr| recursief over een lijst werkt, en dat alle
andere functies die recursief over een lijst werken, ofwel gelijk zijn aan
|foldr|, ofwel applicaties zijn van |foldr|.

Dit wil dus zeggen dat er een wederzijds verband is tussen het type |[a]| en de
functie |foldr|. Als we dit willen veralgemenen, kunnen we ons afvragen of er
dus een bijectie bestaat tussen algebra\"ische datatypes en fold-functies.

Een zodanige bijectie bestaat, en legt het verband tussen een datatype en het
overeenkomstige \emph{catamorfisme}. We kunnen deze catamorfismes eenvoudig
afleiden voor algebra\"ische datatypes.

Om dit beter te verstaan, hebben we het concept van een \emph{algebra} nodig.
Wanneer we een catamorfisme toepassen op een datatype, interpreteren we dit
datatype in een bepaalde algebra, door elke constructor te vervangen door een
operator uit deze algebra. Zo is |sum| als het ware een interpretatie in de
som-algebra, die |:| en |[]| vervangt door respectievelijk |+| en |0|:

\begin{spec}
foldr (+) 0  (1  :  (2  :  (3  :  (4  :  []))))
==           (1  +  (2  +  (3  +  (4  +  0))))
\end{spec}

Dit laat ons toe folds te defini\"eren voor andere datatypes. Beschouw
bijvoorbeeld een eenvoudig boom-type:

\begin{code}
data Tree a
    =  Leaf a
    |  Branch (Tree a) (Tree a)
\end{code}

Door een functie-argument te specifi\"eren voor elke constructor, kunnen we nu
een fold defin\"eren voor het type |Tree|:

\begin{code}
foldTree  ::  (a -> b)       -- Operator voor leaf
          ->  (b -> b -> b)  -- Operator voor branch
          ->  Tree a         -- Input tree
          ->  b              -- Resultaat van de fold
foldTree leaf  _       (Leaf x)      = leaf x
foldTree leaf  branch  (Branch x y)  =
  branch (foldTree leaf branch x) (foldTree leaf branch y)
\end{code}

En met behulp van deze functie kunnen we dus eenvoudig recursieve functies over
bomen schrijven. |sumTree|, bijvoorbeeld, berekent de som van de waarden van de
bladeren van een boom:

\begin{code}
sumTree :: Tree Int -> Int
sumTree = foldTree id (+)
\end{code}

We concluderen dat het een fold voor een bepaald algebra\"isch datatype dus
eenvoudig is af te leiden uit de definitie van dat datatype. Bijgevolg kunnen we
dit ook automatisch doen: we implementeerden een Template Haskell
\cite{sheard2002} \emph{splice} die als parameter de naam van een datatype neemt
en de bijhorende fold genereerd. Zo kan bijvoorbeeld |foldTree| gegenereerd
worden door:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveFold quote Tree "foldTree")
\end{spec}
%}

\section{Folds en Builds}

\TODO{Write this section}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie folds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie builds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Implementatie \& evaluatie}

\begin{itemize}
\item Meer detail
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Related work}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Conclusie}

\begin{itemize}
\item Samenvatting
\item Reflectie
\item Future work...
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{abbrvnat}
\bibliography{references}

\end{document}
