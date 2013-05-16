%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\documentclass[12pt]{report}

\usepackage[dutch]{babel}
\usepackage[font=it]{caption}
\usepackage[left=1.90cm, right=1.90cm, top=1.90cm, bottom=3.67cm]{geometry}
\usepackage[numbers]{natbib}  % For URLs in bibliography
\usepackage[xetex]{graphicx}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{enumitem}
\usepackage{fontspec,xunicode}
\usepackage{listings}
\usepackage{titlesec}
\usepackage{url}

\newcommand{\TODO}[1]{\textbf{(TODO: #1)}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include forall.fmt

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

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
\setmainfont[Ligatures=TeX]{DejaVu Serif}
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

\lstset{basicstyle=\ttfamily, keywordstyle=\ttfamily\bf}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{\futura\Huge Automatische detectie van recursiepatronen}
\author{Jasper Van der Jeugt}

\begin{document}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle
\tableofcontents

\setlength{\parindent}{0.00cm}
\setlength{\parskip}{0.50cm}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Inleiding}

Laten we beginnen bij het begin. Reeds van bij de ontwikkeling van de eerste
computers, naar onze hedendaagse normen vrij rudimentaire machines, was het
noodzakelijk om in de gebruikte programmeertalen \emph{controlestructuren} te
voorzien.  Deze laten toe de manier waarop het programma wordt uitgevoerd te
be\"invloeden. In assembleertaal zijn dit de verschillende \emph{jump}
instructies (\texttt{jmp}, \texttt{je}...). Enkel gebruik maken van simpele
tests en jumps zonder duidelijke consistentie in de manier waarop deze gebruikt
worden kan echter leiden tot "spaghetti code", code die zowel moeilijk te lezen
als te onderhouden is.

In latere programmeertalen (initieel talen zoals ALGOL, en een beetje later ook
C), maakte het concept \emph{gestructureerd programmeren} een opmars.  Dit
betekende dat controlestructuren van een hoger abstractieniveau, zoals
bijvoorbeeld \texttt{for}- en \texttt{while}-lussen, werden ge\"introduceerd.
Deze programmeertalen laten echter meestal wel nog toe om \emph{expliciete}
jumps te maken door middel van de \texttt{goto} instructie.  Dit wordt
ge\"illustreerd in Figuur \ref{figure:for-vs-goto}.

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
  \caption{Twee semantisch equivalente programma's, links \'e\'en met
  hoger-niveau controlestructuren en rechts \'e\'en met \texttt{goto}'s}
  \label{figure:for-vs-goto}
\end{figure}

De versie die gebruikt maakt van \texttt{for} is makkelijker leesbaar voor
programmeurs die bekend zijn met dit concept. Het is immers niet langer nodig om
de labels en \texttt{goto} instructies manueel te matchen en de relatie te
bestuderen: het gebruikte keyword kondigt onmiddelijk de gebruikt
controlestructuur aan (dit wordt meestal ook visueel ondersteund door gebruik te
maken van indentatie).

Ook is het mogelijk formele eigenschappen uit te drukken over programmas die
geschreven zijn in deze stijl, bijvoorbeeld met Floyd-Hoare logica
\cite{floyd1967}. Dit leidde zelfs tot de conclusie dat het gebruik van
\texttt{goto} volledig vermeden moet worden \cite{dijkstra1968}.

Een soortgelijke redenering is te maken over \emph{functionele
programmeertalen}. Deze talen maken geen gebruik van \texttt{goto} instructies,
maar implementeren controlestructuren door middel van \emph{recursie}.

Deze programmeertalen bieden een hoog niveau van abstractie, en moedigen de
programmeurs aan om gebruik te maken van \emph{hogere-orde} functies (bv.
|map|, |filter|, |any|, \ldots). Op deze manier is geen expliciete recursie
nodig. Dit biedt verschillende voordelen:

\begin{itemize}[topsep=0.00cm]
\item Voor een programmeur die bekend is met de gebruikte hogere-orde functies
is mogelijk de code veel sneller te begrijpen: ze herkennen onmiddelijk het
patroon dat aangeboden wordt door de functie en dienen enkel de argumenten van
deze functie te bestuderen.

\item Door gebruik te maken van hogere-orde functies wordt de code beknopter.
Eerder is aangetoond dat het aantal fouten in code proportioneel is tot de
grootte van de codebase \cite{gaffney1984}. Hieruit kunnen we concluderen dat
het gebruik van hogere-orde functies het aantal fouten in programmas zou moeten
reduceren.

\item Het is mogelijk eigenschappen \'e\'enmaal te bewijzen over een
hogere-orde functie voor willekeurige argumenten. Dit spaart ons werk uit als
we willen redeneren over code, want de resultaten van deze bewijzen gelden dan
voor elke applicatie van deze hogere-orde functie.

\item Ook de compiler kan gebruik maken van deze eigenschappen, om verschillende
optimalisaties uit te voeren op de code.
\end{itemize}

Deze redenen vormen een sterke motivatie om in deze talen geen expliciete
recursie te gebruiken wanneer een hogere-orde functie beschikbaar is. Toch
blijkt dat veel programmeurs nog gebruik maken van expliciete recursie.

Enkele redenen hiervoor zijn bijvoorbeeld dat de programmeur niet bekend is met
de hogere-orde functie, of dat er geen tijd is om de functie te refactoren. We
zien zelfs dat we voorbeelden terugvinden van expliciete recursie in code
geschreven door geavanceerde gebruikers van functionele programmeertalen
\TODO{cite: GHC HQ does it}.

De voordelen die hierboven beschreven staan vormen een motivatie om te
onderzoeken of het niet mogelijk is om deze functies, geschreven in expliciet
recursieve stijl, automatisch om te zetten in functies die gebruik maken van de
hogere-orde hulpfuncties. Op die manier kan de programmeur code schrijven in om
het even welke stijl, en toch genieten van de verschillende optimalisaties.

In dit document beschrijven we een aanpak om dit mogelijk te maken. Meer
concreet:

\begin{itemize}[topsep=0.00cm]

\item We tonen aan hoe functies die expliciete recursie gebruiken maar wel een
specifiek soort patroon (meer bepaald \emph{catamorfismes}) volgen kunnen
gedetecteerd worden, en vertaald naar een versie die een hogere-orde |fold|
functie gebruikt in plaats van expliciete recursie.

\item Tevens leggen we ook uit hoe we functies die geschreven kunnen worden als
een toepassing van |build| kunnen detecteren en vertalen naar een versie die
effectief gebruikt maakt van |build|. Merk op dat |build| op zich geen
hogere-orde functie is, maar dat we zowel |fold| als |build| nodig hebben om
\emph{foldr/build-fusion} toe te passen, een bekende optimalisatie.

\item We implementeerden een GHC Compiler Plugin die deze detecties en
vertalingen automatisch kan uitvoeren tijdens de compilatie van een
Haskell-programma. Deze plugin werkt zowel voor de typische folds over lijsten
in Haskell (|[a]|), maar ook voor andere (direct) recursieve datatypes,
gedefini\"eerd door de gebruiker.

\item We onderzochten het aantal functies in enkele bekende Haskell programmas
die kunnen herschreven worden met behulp van de hogere orde functie |fold|. Deze
blijken in vele packages aanwezig te zijn. Ook bekijken we de resultaten van
enkele benchmarks na automatische |foldr/build-fusion|. Omdat
|foldr/build-fusion| de compiler toelaat om tussentijdse allocatie te vermijden,
zien we hier zeer grote speedups.

\end{itemize}

\TODO{Kort overzicht van de verschillende hoofdstukken}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

We kozen voor de pure functionele programmeertaal Haskell \cite{jones2003}
omwille van verschillende redenen:

\begin{itemize}[topsep=0.00cm]

\item Een grote variatie aan hogere-orde functies is beschikbaar. Voor lijsten
worden vele zelfs beschikbaar gesteld in het Prelude, de module die impliciet in
elk Haskell-programma wordt ge\"importeerd. Zo is bijvoorbeeld |foldr|
beschikbaar zonder ook maar \'e\'en library te moeten importeren! Verdere folds,
ook over andere datatypes, zijn beschikbaar in aanvullende libraries.

\item Haskell is een sterk getypeerde programmeertaal. Na het ini\"ele parsen en
typechecken van de code is deze type-informatie is beschikbaar in elke stap van
de compilatie. Deze types geven ons meer informatie die we kunnen gebruiken in
de transformaties.

\item De de-facto standaard Haskell Compiler, GHC \cite{ghc}, laat via een
plugin-systeem toe om code te manipuleren op een relatief eenvoudige manier
\TODO{Cite het deel over GHC plugins/implementatie...}.

\end{itemize}

In dit hoofdstuk geven we een zeer beknopt overzicht van Haskell, en lichten we
ook enkele relevante hogere-orde functies toe.

\section{Haskell: types en functies}

Haskell is ontstaan uit de lambda-calculus, een formeel systeem om aan logisch
redeneren te doen, met een zeer eenvoudige syntax. Het is dan ook logisch om
hieruit te vertrekken.

\begin{spec}
e ::= x        -- Een variabele
   |  e e      -- Functie-applicatie (links-associatief)
   |  \x -> e  -- Functie-abstractie (rechts-associatief)
\end{spec}

Dit is natuurlijk een zeer beperkte syntax en Haskell breidt deze sterk uit.
Beschouw bijvoorbeeld de volgende Haskell-functie (links) en het lambda-calculus
equivalent (rechts):

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
Deze type-signatuur is dus equivalent aan |Float -> (Float -> Float)|. Dit
concept heet \emph{currying}: we kunnen |middle| beschouwen als een functie die
twee |Float|-argumenten neemt en een |Float| als resultaatwaarde heeft, of als
een functie die \'e\'en Float argument neemt en functie van het type |Float ->
Float| als resultaatwaarde heeft.

In de lambda-calculus is het niet mogelijk om direct recursieve functies te
schrijven. In de plaats daarvan dient er een omweg gemaakt te worden via een
\emph{fixpoint-combinator}. Een fixpoint-combinator is een functie |g| zodanig
dat geldt voor elke functie |f|: |g f = f (g f)|. Hierdoor is het mogelijk een
functie door te geven voor een recursieve oproep, zonder deze functie expliciet
een naam te geven.

E\'en van de de bekendste voorbeelden hiervan is de \emph{Y-combinator}.

\newtheorem{theorem:y-combinator}{Definitie}[section]
\begin{theorem:y-combinator}\label{theorem:y-combinator}
\[ |Y = \f -> (\x -> f (x x)) (\x -> f (x x))| \]
\end{theorem:y-combinator}

\begin{proof}
We kunnen eenvoudig aantonen dat dit wel degelijk een fixpoint-combinator is.

\begin{spec}
    Y f

== {- def |Y| -}

    (\f -> (\x -> f (x x)) (\x -> f (x x))) f

== {- $\beta$-reductie -}

    (\x -> f (x x)) (\x -> f (x x)))

== {- $\beta$-reductie -}

    f ((\x -> f (x x)) (\x -> f (x x)))

== {- $\lambda$-abstractie -}

    f ((\f -> (\x -> f (x x)) (\x -> f (x x))) f)

== {- def |Y| -}

    f (Y f)
\end{spec}
\end{proof}

In tegenstelling tot de lambda-calculus is het is Haskell niet nodig om gebruik
te maken van fixpoint-combinators: men kan eenvoudig expliciet recursieve
definities geven door de functie zelf bij naam aan te roepen.

\begin{code}
fib :: Int -> Int
fib n = if n <= 1 then 1 else fib (n - 1) + fib (n - 2)
\end{code}

Verder breidt Haskell de lambda-calculus uit met \emph{algebra\"ische datatypes}
en \emph{pattern matching}. Een algebra\"isch datatype is in Haskell typisch een
\emph{somtype} (keuze tussen verschillende types) van \emph{producttypes}
(combinatie van verschillende types).

Beschouw het volgende voorbeeld:

\begin{code}
data Topping = Salami | Mozarella | Peppers

data Pizza
    =  Plain
    |  ExtraToppings Topping Topping
\end{code}

|Topping| is een somtype met drie verschillende constructoren zonder meer
informatie. |Pizza| is ook een somtype van twee verschillende constructoren,
waarvan \'e\'en een producttype is van twee |Topping|-types.

Met behulp van pattern-matching kan de onderliggende constructor onderzocht
worden:

\begin{code}
toppingPrice :: Topping -> Double
toppingPrice Salami     = 0.50
toppingPrice Mozarella  = 0.50
toppingPrice Peppers    = 0.30

pizzaPrice :: Pizza -> Double
pizzaPrice Plain                  = 5.20
pizzaPrice (ExtraToppings t1 t2)  = 5.40 + toppingPrice t1 + toppingPrice t2
\end{code}

Het typesysteem van Haskell is zeer complex en valt buiten de scope van dit
werk. Een interessante feature die we wel nodig hebben is
\emph{type-polymorfisme}. Dit laat ons toe om met \'e\'enzelfde set functies en
datatypes te werken met waarden van verschillende types. Beschouw bijvoorbeeld
de functie |id|, de identiteitsfunctie. Deze functie kan op een waarde van
om het even welk type toegepast worden en is bijgevolg polymorf.

\begin{code}
id :: a -> a
id x = x
\end{code}

Polymorfe datatypes zijn ook mogelijk in Haskell. Een voorbeeld hiervan is de
lijst: we kunnen voor elk mogelijk type een lijst maken met waarden van dit type
door de dezelfde constructoren |:| en |[]| te gebruiken.

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

Deze patronen kunnen ge\"implementeerd worden door middel van hogere-orde
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

Andere voorbeelden van hogere-orde functies zijn |map| en |filter|. |map| laat
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
\label{section:universal-fold}

Het feit dat we zowel |map| als |filter| schrijven met behulp van |foldr| duidt
aan dat |foldr| een zeer interessante functie is. Meer bepaald, de universele
eigenschap van fold \cite{hutton1999} is weergegeven in definitie
\ref{theorem:universal-fold}.

\newtheorem{theorem:universal-fold}{Definitie}[section]
\begin{theorem:universal-fold}\label{theorem:universal-fold}
\[
  |g = foldr f v|
  ~~~~~~~ \Leftrightarrow
  \begin{minipage}[c]{0.30\textwidth}
  \begin{spec}
g []        = v
g (x : xs)  = f x (g xs)
  \end{spec}
  \end{minipage}
\]
\end{theorem:universal-fold}

Concreet wil dit voor ons zeggen dat als we een |f| en |v| kunnen vinden die aan
de vereiste eigenschappen voldoen, dat we |g| kunnen herschrijven als een
|foldr|.

Ook betekent dit dat er slechts \'e\'en |foldr| is voor een lijst -- elke
alternatieve definitie is hieraan isomorf. Er is dus een wederzijds verband
tussen het type |[a]| en de functie |foldr|. Als we dit willen veralgemenen,
kunnen we ons afvragen of er dus een bijectie bestaat tussen algebra\"ische
datatypes en fold-functies.

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

Dit idee laat ons toe folds te defini\"eren voor andere datatypes. Beschouw
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

We concluderen dat een fold voor een bepaald algebra\"isch datatype dus
eenvoudig is af te leiden uit de definitie van dat datatype. Bijgevolg kunnen we
dit ook automatisch doen.

Template Haskell \cite{sheard2002} is een Haskell-extensie die toelaat om aan
type-safe compile-time meta-programmeren te doen. Op deze manier kunnen we
Haskell manipuleren met Haskell.

We implementeerden een algoritme in Template Haskell om de fold horende bij een
datatype automatisch te genereren. Zo kan bijvoorbeeld |foldTree| gegenereerd
worden door:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveFold quote Tree "foldTree")
\end{spec}
%}

Het algoritme werkt als volgt. We gebruiken de types |Tree a| en |[a]| als
voorbeelden.

\begin{enumerate}

\item De fold neemt als laatste argument altijd een waarde van het opgegeven
type, en geeft een waarde van het type |b| terug.

\begin{spec}
foldTree :: ... -> Tree a -> b
foldList :: ... -> [a] -> b
\end{spec}

\item Per constructor wordt er een extra argument meegeven.

\begin{spec}
foldTree :: <LeafArg> -> <NodeArg> -> Tree a -> b
foldList :: <ConsArg> -> <NilArg> -> [a] -> b
\end{spec}

\item Wat zijn nu de concrete types van deze argumenten? Laten we eerst de types
van de constructoren beschouwen:

\begin{spec}
Leaf  :: a -> Tree a
Node  :: Tree a -> Tree a -> Tree a

(:)   :: a -> [a] -> [a]
[]    :: [a]
\end{spec}

\item Deze constructoren geven de subtermen aan en corresponderen dus met de
verschillende argumenten. De recursie wordt echter afgehandeld door de |fold|
functie, en dus is elke recursieve subterm al gereduceerd tot een waarde van het
type |b|. Eveneens is |b| het type van het resultaat. We vinden:

\begin{spec}
<LeafArg>  = a -> b
<NodeArg>  = b -> b -> b

<ConsArg>  = a -> b -> b
<NilArg>   = b
\end{spec}

En dus:

\begin{spec}
foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldList :: (a -> b -> b) -> b -> [a] -> b
\end{spec}

\item Eens de type-signaturen bepaald zijn is het genereren van de implementatie
redelijk eenvoudig. Elke functieparameter krijgt een naam naar de constructor.
Vervolgens genereren we een |go| functie. Dit is een toepassing van de Static
Argument Transformation (zie \TODO{Cite SAT}).

\begin{spec}
foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldTree leaf node = go
  where
    go (Leaf x)    = leaf x
    go (Node x y)  = node (go x) (go y)

foldList :: (a -> b -> b) -> b -> [a] -> b
foldList cons nil = go
  where
    go (x : y)  = cons x (go y)
    go []       = nil
\end{spec}

De |go| functie inspecteert simpelweg de constructor en roept dan het
corresponderende functie-argument met als argumenten de gereduceerde subtermen.
Een gereduceerde niet-recursieve subterm |t| is gewoon die subterm |t|, en voor
een recursieve subterm is dit |go t|.

\end{enumerate}

\section{Fusion: Folds en Builds}

\subsection{Wat is fusion?}

Naast de verschillende voordelen op vlak van \emph{refactoring}, is het ook
mogelijk \emph{optimalisaties} door te voeren op basis van deze hogere-orde
functions.

Beschouw de volgende twee versies van een functie die de som van de kwadraten
van de oneven nummers in een lijst berekenen:

\begin{code}
sumOfSquaredOdds :: [Int] -> Int
sumOfSquaredOdds []  = 0
sumOfSquaredOdds (x : xs)
    | odd x          = x ^ 2 + sumOfSquaredOdds xs
    | otherwise      = sumOfSquaredOdds xs
\end{code}

\begin{code}
sumOfSquaredOdds' :: [Int] -> Int
sumOfSquaredOdds' = sum . map (^ 2) . filter odd
\end{code}

Ervaren Haskell-programmeurs zullen steevast de tweede versie boven de eerste
verkiezen. Het feit dat de tweede versie is opgebouwd uit kleinere, makkelijk te
begrijpen functies maakt deze veel leesbaarder.

De eerste versie lijkt echter effici\"enter: deze berkent rechtstreeks het
resultaat (een |Int|), terwijl de tweede versie twee tijdelijke |[Int]| lijsten
aanmaakt: \'e\'en als resultaat van |filter odd|, en nog een tweede als
resultaat van |map (^ 2)|.

In de ideale situatie willen we dus de effici\"entie van de eerste versie
combineren met de leesbaarheid van de tweede versie. Dit wordt mogelijk gemaakt
door \emph{fusion} \cite{wadler1990} \cite{gill1993}.

We kunnen fusion best uitleggen door te starten met een eenvoudig voorbeeld:
\emph{map/map-fusion}. Dit is een transformatie die gegeven wordt door de
definitie \ref{theorem:map-map-fusion}.

\newtheorem{theorem:map-map-fusion}{Definitie}[section]
\begin{theorem:map-map-fusion}\label{theorem:map-map-fusion}
\[ |map f . map g| ~~ |==| ~~ |map (f . g)| \]
\end{theorem:map-map-fusion}

Deze equivalentie is eenvoudig te bewijzen via inductie.

\begin{proof}
We bewijzen dit eerst voor de lege lijst |[]|. Voor |map f . map g| krijgen we:

\begin{spec}
    map f (map g [])

== {- def |map []| -}

    map f []

== {- def |map []| -}

    []
\end{spec}

En voor |map (f . g)| krijgen we:

\begin{spec}

    map (f . g) []

== {- def |map []| -}

    []
\end{spec}

We nemen nu aan dat map/map-fusion correct is voor een willekeurige lijst |xs|
en bewijzen dat de correctheid dan ook geldt voor een lijst |x : xs|.

\begin{spec}
    map f (map g (x : xs))

== {- def |map :| -}

    map f (g x : map g xs)

== {- def |map :| -}

    f (g x) : map f (map g xs)

== {- inductiehypothese -}

    f (g x) : map (f . g) xs

== {- def |map :| -}

    map (f . g) (x : xs)
\end{spec}
\end{proof}

GHC beschikt over een mechanisme om dit soort transformaties uit te voeren
tijdens de compilatie, door middel van het \texttt{RULES} pragmas
\cite{jones2001}. Zo kunnen we bijvoorbeeld map/map-fusion implementeren door
eenvodigweg het volgende pragma te vermelden:

\begin{lstlisting}
{-# RULES "map/map-fusion" forall f g xs.
    map f (map g xs) = map (f . g) xs #-}
\end{lstlisting}

Het nadeel van deze aanpak is echter dat het aantal nodige rules kwadratisch
stijgt in proportie tot het aantal hogere-orde functies dat op het datatype (in
dit geval lijsten) werkt.

Ter illustratie, als we bijvoorbeeld enkel de functies |map| en |filter|
beschouwen, hebben we al vier rules nodig, en een additonele hulpfunctie
|mapFilter|:

\begin{spec}
map f . map g        = map (f . g)
map f . filter g     = mapFilter f g
filter f . map g     = filter (f . g)
filter f . filter g  = filter (\x -> f x && g x)

mapFilter :: (a -> b) -> (a -> Bool) -> [a] -> [b]
mapFilter _ _ []  = []
mapFilter f g (x : xs)
    | g x         = f x : mapFilter f g xs
    | otherwise   = mapFilter f g xs
\end{spec}

Voor sommige modules ligt het aantal hogere-orde functies zeer hoog, dus wordt
deze aanpak onhaalbaar.

\subsection{Foldr/build-fusion}

Dit probleem wordt opgelost met \emph{foldr/build-fusion}. We kunnen |foldr|
beschouwen als een algemene manier om lijsten te \emph{consumeren}. Hiervan is
|build| de tegenhanger: een algemene manier om lijsten te \emph{produceren}.

\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}

We kunnen nu bijvoorbeeld |map| en |filter| met behulp van |build|:

\begin{spec}
map :: (a -> b) -> [a] -> [b]
map f ls = build $ \cons nil ->
    foldr (\x xs -> cons (f x) xs) nil ls

filter :: (a -> Bool) -> [a] -> [a]
filter f ls = build $ \cons nil ->
    foldr (\x xs -> if f x then cons x xs else xs) nil ls
\end{spec}

Het nut van |build| wordt nu duidelijk: we gebruiken deze functie om te
\emph{abstraheren} over de concrete constructoren: in plaats van |:| en |[]|
gebruiken we nu de abstracte |cons| en |nil|.

Intu\"itief laat dit ons toe om de constructoren |:| en |[]| te \emph{vervangen}
door andere functies -- en zoals we in Sectie \ref{section:universal-fold}
zagen, kunnen we het toepassen van |foldr| net beschouwen als het vervangen van
de constructoren door de argumenten van |foldr|!

Dit idee laat ons toe om een de productie en consumatie van een lijst te fusen,
zodanig dat er geen tijdelijke lijst moet worden aangemaakt. We werken dit nu
formeel uit.

\newtheorem{theorem:foldr-build-fusion}{Definitie}[section]
\begin{theorem:foldr-build-fusion}\label{theorem:foldr-build-fusion}
Als

\[ |g :: forall b. (a -> b -> b) -> b -> b| \]

dan

\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]
\end{theorem:foldr-build-fusion}

\begin{proof}
Van het type van een polymorfe functie kan een \emph{gratis theorie} afgeleid
worden \cite{wadler1989}. Zo krijgen we voor |g| dat voor alle |f|, |f'| en |h|
met als types:

\[ |f :: A -> B -> B|, |f' :: A -> B' -> B'|, |h :: B -> B'| \]

de volgende implicatie geldt:

\[ |(forall a b. h (f a b) == f' a (h b))|
    \Rightarrow |(forall b. h (g f b) == g f' (h b))| \]

We kunnen deze implicatie nu instanti\"eren met:

\[ |f = (:)|, |f' = cons|, |h = foldr cons nil| \]

We krijgen dus:

\begin{align*}
|(forall a b. foldr cons nil (a : b) == cons a (foldr cons nil b))|
    \Rightarrow \\
    |(forall b. foldr cons nil (g (:) b) == g cons (foldr cons nil b))|
\end{align*}

De linkerkant van de implicatie is triviaal geldig: dit is gewoon de definitie
van |foldr| voor een niet-ledige lijst. Hieruit volgt dat:

\[ |(forall b. foldr cons nil (g (:) b) == g cons (foldr cons nil b))| \]

Deze gelijkheid kunnen we opnieuw instanti\"eren, ditmaal met |b = []|. Zo
krijgen we:

\begin{spec}
    foldr cons nil (g (:) []) == g cons (foldr cons nil [])

== {- def |foldr []| -}

    foldr cons nil (g (:) []) == g cons nil

== {- def |build| -}

    foldr cons nil (build g) == g cons nil
\end{spec}

\end{proof}

Ter illustratie tonen we nu hoe met deze enkele fusie-regel onze elegantere
versie van |sumOfSquaredOdds'| automatisch door GHC kan worden omgezet naar een
performante versie.

\begin{spec}
    sumOfSquaredOdds'

== {- inline |sumOfSquaredOdds'| -}

    sum . map (^ 2) . filter odd

== {- inline |.| -}

    \ls -> sum (map (^ 2) (filter odd ls))

== {- inline |filter| -}

    \ls -> sum (map (^ 2)
        (build $ \cons nil ->
            foldr (\x xs -> if odd x then cons x xs else xs) nil ls))

== {- inline |map| -}

    \ls -> sum
        (build $ \cons' nil' ->
            foldr (\x xs -> cons' (x ^ 2) xs) nil'
                (build $ \cons nil ->
                    foldr (\x xs -> if odd x then cons x xs else xs) nil ls))

== {- foldr/build-fusion -}

    \ls -> sum
        (build $ \cons' nil' ->
            (\cons nil ->
                foldr (\x xs -> if odd x then cons x xs else xs) nil ls)
            (\x xs -> cons' (x ^ 2) xs)
            nil')

== {- $\beta$-reductie -}

    \ls -> sum
        (build $ \cons' nil' ->
            foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls)

== {- inline |sum| -}

    \ls -> foldr (+) 0
        (build $ \cons' nil' ->
            foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls)

== {- foldr/build-fusion -}

    \ls -> (\cons' nil' ->
        foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls) (+) 0

== {- $\beta$-reductie -}

    \ls -> foldr (\x xs -> if odd x then (x ^ 2) + xs else xs) 0 ls

\end{spec}

Finaal is |sumOfSquaredOdds'| dus volledig gereduceerd tot \'e\'en enkele
|foldr| over een lijst: het is niet meer nodig om tijdelijke lijsten te
alloceren om het resultaat te berekenen. In \TODO{Cite results chapter} tonen we
aan dat dit leid tot significante speedups.

We krijgen dus als het ware het beste van beide werelden: we kunnen elegante
definities gebruiken voor de functies, die eenvoudiger leesbaar zijn een
makkelijker onderhoudbaar; maar tevens worden deze vertaald door de compiler tot
snelle, geoptimaliseerde versies.


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
