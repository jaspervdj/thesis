%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\documentclass[12pt]{report}

\usepackage[dutch]{babel}
\usepackage[font={footnotesize, it}]{caption}
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
import Data.Char  (toUpper)
import Data.List  (intersperse)
import GhcPlugins
import Prelude    hiding (filter, foldr, head, id, map, sum, product,
                          replicate)

elapsed :: a
elapsed = undefined
\end{code}
}

%format e1 = e"_1"
%format e2 = e"_2"
%format f1 = f"_1"
%format f2 = f"_2"
%format B1 = B"_1"
%format B2 = B"_2"
%format x1 = x"_1"
%format x2 = x"_2"
%format xs1 = xs"_1"
%format xs2 = xs"_2"
%format elapsed = "\ldots"
%format subst (term) (v) (e) = [v "\mapsto" e] term

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
voorzien. Deze instructies laten toe de manier waarop het programma wordt
uitgevoerd te be\"invloeden. In assembleertaal zijn dit de verschillende
\emph{sprong} instructies (\texttt{jmp}, \texttt{je}...). Typisch zal de
instructie voor de spronginstructie een testinstructie zijn. Enkel gebruik maken
van simpele tests en sprongen zonder duidelijke consistentie in de manier waarop
deze gebruikt worden kan echter leiden tot zogenaamde "spaghetti code". Daarmee
bedoelen we code die zowel moeilijk te lezen als te onderhouden is.

In latere programmeertalen (initieel talen zoals ALGOL, gevolgd door talen als
C), maakte het concept \emph{gestructureerd programmeren} een opmars.  Dit
betekent dat controlestructuren van een hoger abstractieniveau, zoals
bijvoorbeeld \texttt{for}- en \texttt{while}-lussen, werden ge\"introduceerd.
Deze programmeertalen laten echter meestal wel nog toe om \emph{expliciete}
sprongen te maken door middel van de \texttt{goto} instructie \footnote{Merk op
dat deze programmeertalen door een compiler worden omgezet naar machinetaal,
waarin wel nog sprongen voorkomen. Dit vormt echter geen probleem voor
leesbaarheid, sinds de meeste programmeurs deze machinetaal slechts zelden
zullen bekijken.}. Dit wordt ge\"illustreerd in Figuur \ref{figure:for-vs-goto}.

\begin{figure}[h]
  \begin{minipage}[t]{0.5\textwidth}
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
  \begin{minipage}[t]{0.5\textwidth}
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
  \caption{Twee semantisch equivalente programma's in de programmeertal C, links
  \'e\'en met hoger-niveau controlestructuren en rechts \'e\'en met
  \texttt{goto}'s.}
  \label{figure:for-vs-goto}
\end{figure}

De versie die gebruikt maakt van \texttt{for} is eenvoudiger leesbaar voor
programmeurs die bekend zijn met dit concept. Het is immers niet langer nodig om
de labels en \texttt{goto} instructies manueel te matchen en de relatie te
bestuderen: het gebruikte keyword kondigt onmiddelijk de gebruikt
controlestructuur aan (dit wordt meestal ook visueel ondersteund door gebruik te
maken van indentatie).

Bovendien is het mogelijk formele eigenschappen uit te drukken over programma's
die geschreven zijn in deze stijl, bijvoorbeeld met Floyd-Hoare logica
\cite{floyd1967}. Dit leidde zelfs tot de conclusie dat het gebruik van
\texttt{goto} volledig vermeden moet worden \cite{dijkstra1968}.

Een soortgelijke redenering is te maken over \emph{functionele
programmeertalen}. Deze talen maken geen gebruik van \texttt{goto} instructies,
maar implementeren controlestructuren door middel van \emph{recursie}.

Deze programmeertalen bieden een hoog abstractieniveau, en moedigen de
programmeurs aan om gebruik te maken van \emph{hogere-orde} functies (bv.
|map|, |filter|, |any|, \ldots). Op deze manier is geen expliciete recursie
nodig. Dit biedt verschillende voordelen:

\begin{enumerate}[topsep=0.00cm]
\item Voor een programmeur die bekend is met de gebruikte hogere-orde functies
is mogelijk de code veel sneller te begrijpen \cite{dubochet2009}: men herkent
onmiddelijk het patroon dat aangeboden wordt door de functie en dient enkel de
argumenten van deze functie te bestuderen.

\item Door gebruik te maken van hogere-orde functies wordt de code beknopter.
Eerder is aangetoond dat het aantal fouten in code proportioneel is tot de
grootte van de codebase \cite{gaffney1984}. Hieruit kunnen we concluderen dat
het gebruik van hogere-orde functies het aantal fouten in programma's zou moeten
reduceren.

\item Het is mogelijk eigenschappen \'e\'enmaal te bewijzen over een
hogere-orde functie voor willekeurige argumenten. Dit spaart ons werk uit als
we willen redeneren over code, want de bewijzen gelden dan voor elke applicatie
van deze hogere-orde functie.

\item Ook de compiler kan gebruik maken van deze eigenschappen, om verschillende
optimalisaties uit te voeren op de code.
\end{enumerate}

Deze redenen vormen een sterke motivatie om in deze talen geen expliciete
recursie te gebruiken als een hogere-orde functie beschikbaar is. Toch blijkt
dat veel programmeurs nog gebruik maken van expliciete recursie.

Enkele redenen hiervoor zijn bijvoorbeeld dat de programmeur niet bekend is met
de hogere-orde functie, of dat er geen tijd is om zijn zelfgeschreven functie te
herschrijven op basis van bestaande hogere-orde functies. We zien zelfs dat we
voorbeelden terugvinden van expliciete recursie in code geschreven door
gevorderde gebruikers van functionele programmeertalen \TODO{cite: GHC HQ does
it}.

De hierboven beschreven voordelen vormen de basismotivatie voor het onderzoek
dat we in deze thesis vericht hebben. We richten ons op functies die geschreven
zijn in een expliciete recursieve stijl en onderzoeken in welke gevallen het
mogelijk is deze automatisch om te zetten in functies die gebruik maken van de
hogere-orde hulpfuncties. Op die manier kan de programmeur code schrijven in om
het even welke stijl, en toch genieten van de verschillende optimalisaties.

We hanteren hiervoor de volgende concrete aanpak:

\TODO{Verwijs meer naar hoofdstukken hier}

\begin{enumerate}[topsep=0.00cm]

\item We tonen aan hoe functies die expliciete recursie gebruiken maar wel een
specifiek soort patroon (meer bepaald \emph{catamorfismes} \TODO{citatie?})
volgen kunnen gedetecteerd worden, en vertaald naar een versie die een
hogere-orde |fold| functie gebruikt in plaats van expliciete recursie.

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

\item We onderzochten het aantal functies in enkele bekende Haskell programma's
die kunnen herschreven worden met behulp van de hogere orde functie |fold|. Deze
blijken in vele packages aanwezig te zijn. Ook bekijken we de resultaten van
enkele benchmarks na automatische |foldr/build-fusion|. Omdat
|foldr/build-fusion| de compiler toelaat om tussentijdse allocatie te vermijden,
zien we hier zeer grote versnellingen.

\end{enumerate}

We kozen Haskell als programmeertaal voor ons onderzoek. In het volgende
hoofdstuk zullen we kort ingaan op de eigenschappen van deze programmeertaal die
we gebruiken in deze thesis.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

We kozen voor de pure functionele programmeertaal Haskell \cite{jones2003}
omwille van verschillende redenen:

\begin{itemize}[topsep=0.00cm]

\item Het Haskell Prelude \footnote{Het Prelude is de module die impliciet in
elk Haskell-programma wordt ge\"importeerd. De functies hieruit zijn dus
rechtstreeks te gebruiken zonder dat men een library moet importeren.} en de
beschikbare libraries bieden een waaier aan hogere-orde functies aan.

\item Haskell is een sterk getypeerde programmeertaal. Na het ini\"ele parsen en
typechecken van de code is deze type-informatie is beschikbaar in elke stap van
de compilatie. Deze types geven ons meer informatie die we kunnen gebruiken in
de transformaties. Bovendien maakt Haskell gebruik van type inference
\TODO{cite}, wat ervoor zorgt dat de programmeur meestal zelf geen types moet
opgeven.

\item De de-facto standaard Haskell Compiler, GHC \cite{ghc}, laat via een
plugin-systeem toe om code te manipuleren op een relatief eenvoudige manier
\TODO{Cite het deel over GHC plugins/implementatie...}.

\end{itemize}

In dit hoofdstuk geven we een zeer beknopt overzicht van Haskell, en lichten we
ook enkele relevante hogere-orde functies toe.

\section{Haskell: types en functies}

Haskell is gebaseerd op de lambda-calculus. Dit is een formeel, doch eenvoudig
systeem, om aan logisch redeneren te doen. Het beschikt over een zeer beperkt
aantal basisoperaties. We beginnen onze Haskell-introductie dan ook bij de
lambda-calculus.

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

Net zoals lambda-abstracties is de |->| (een operator op type-niveau) in
type-signaturen rechts-associatief.  Deze type-signatuur is dus equivalent aan
|Float -> (Float -> Float)|. Dit concept heet \emph{currying}: we kunnen
|middle| beschouwen als een functie die \'e\'en Float argument neemt en functie
van het type |Float -> Float| als resultaatwaarde heeft, of als een functie die
twee |Float|-argumenten neemt en een |Float| als resultaatwaarde heeft.

In de lambda-calculus is het niet mogelijk om direct recursieve functies te
schrijven. Er bestaat echter een elegante oplossing: de
\emph{fixpoint-combinator}. Een fixpoint-combinator is een functie |g| waarvoor
geldt dat voor elke functie |f|: |g f = f (g f)|. Hierdoor is het mogelijk een
functie door te geven voor een recursieve oproep, zonder deze functie expliciet
een naam te geven.

E\'en van de de bekendste voorbeelden hiervan is de \emph{Y-combinator}.

\newtheorem{theorem:y-combinator}{Definitie}[section]
\begin{theorem:y-combinator}\label{theorem:y-combinator}
\[ |Y = \f -> (\x -> f (x x)) (\x -> f (x x))| \]
\end{theorem:y-combinator}

\newtheorem*{theorem:y-fixpoint}{Stelling}
\begin{theorem:y-fixpoint}\label{theorem:y-fixpoint}
|Y| is een fixpoint-combinator, dus:

\[ |Y f == f (Y f)| \]
\end{theorem:y-fixpoint}

\begin{proof}
~ \newline
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

In tegenstelling tot de lambda-calculus is het in Haskell niet nodig om gebruik
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

Het zou ons te ver voeren om het volledig typesysteem van Haskell hier te
bespreken. We beperken ons dan ook tot de kenmerken die we nodig hebben in deze
scriptie. Een belangrijk en bijzonder interessant kenmerk van het typesysteem
dat we doorheen deze thesis gebruiken is \emph{type-polymorfisme}. Dit laat ons
toe om met \'e\'enzelfde set functies en datatypes te werken met waarden van
verschillende types. Beschouw bijvoorbeeld de identiteitsfunctie |id|. Deze
functie kan op een waarde van om het even welk type toegepast worden en is
bijgevolg polymorf.

\begin{code}
id :: a -> a
id x = x
\end{code}

Behalve polymorfe functies bestaan er ook polymorfe datatypes. Een voorbeeld
hiervan is de lijst: we kunnen voor elk mogelijk type een lijst maken met
waarden van dit type door de dezelfde constructoren |(:)| en |[]| te gebruiken.

\begin{spec}
data [a]
    =  a : [a]
    |  []
\end{spec}

Lijsten zijn alomtegenwoordig in functionele programma's en verdienen speciale
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

Omdat recursieve functies over lijsten alomtegenwoordig zijn, is het vaak
mogelijk patronen te onderscheiden. Beschouw even de volgende twee functies,
|sum| en |product|.

\begin{code}
sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs

product :: [Int] -> Int
product []        = 1
product (x : xs)  = x * product xs
\end{code}

Deze patronen kunnen ge\"implementeerd worden door middel van hogere-orde
functies: functies die andere functies als parameters nemen.  In het
bovenstaande voorbeeld zijn de functies eenvoudige voorbeelden van het |foldr|
patroon.

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _  z []        = z
foldr f  z (x : xs)  = f x (foldr f z xs)
\end{code}

Als we |sum| en |product| herschrijven op basis van |foldr|, krijgen we veel
beknoptere definities, die semantisch equivalent zijn aan de expliciet
recursieve versies en sneller te lezen door ervaren programmeurs:

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

De |filter|-functie wordt gebruikt om bepaalde elementen uit een lijst te
selecteren:

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
eigenschap van fold \cite{hutton1999} is weergegeven in stelling
\ref{theorem:universal-fold}.

\newtheorem{theorem:universal-fold}{Stelling}[section]
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

Concreet betekent dit dat we een functie |g| kunnen herschrijven in termen van
|foldr| zodra we een |f| en |v| vinden die aan de bovenstaande voorwaarden
voldoen.

Ook betekent dit dat er slechts \'e\'en |foldr| is voor een lijst -- elke
alternatieve definitie is hieraan isomorf. Er is dus een wederzijds verband
tussen het type |[a]| en de functie |foldr|. De vraag naar het bestaan van een
bijectie tussen algebra\"ische datatypes en fold-functies dringt zich dus op.

Deze vraag kan affirmatief beantwoord worden: een dergelijke bijectie bestaat,
ze legt bovendien het verband tussen een datatype en het overeenkomstige
\emph{catamorfisme}: de unieke manier om een algebra\"isch datatype stap voor
stap te reduceren tot \'e\'en enkele waarde. We kunnen deze catamorfismes
eenvoudig afleiden voor algebra\"ische datatypes.

Om dit beter te verstaan, hebben we het concept van een \emph{algebra} nodig.
Wanneer we een catamorfisme toepassen op een datatype, interpreteren we dit
datatype in een bepaalde algebra, door elke constructor te vervangen door een
operator uit deze algebra. Zo is |sum| als het ware een interpretatie in de
som-algebra, die |(:)| en |[]| vervangt door respectievelijk |+| en |0|:

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

% For testing
\ignore{
\begin{code}
instance Show a => Show (Tree a) where
    show = foldTree
        (\x   -> "(Leaf " ++ show x ++ ")")
        (\l r -> "(Branch " ++ l ++ " " ++ r ++ ")")
\end{code}
}

Door een functie-argument te specificeren voor elke constructor, kunnen we nu
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
foldTree  :: ... -> Tree a -> b
foldList  :: ... -> [a] -> b
\end{spec}

\item Per constructor wordt er een extra argument meegeven.

\begin{spec}
foldTree  :: <LeafArg> -> <NodeArg> -> Tree a -> b
foldList  :: <ConsArg> -> <NilArg> -> [a] -> b
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
foldTree  :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldList  :: (a -> b -> b) -> b -> [a] -> b
\end{spec}

\item Eens de type-signaturen bepaald zijn is het genereren van de implementatie
redelijk eenvoudig. Elke functieparameter krijgt een naam naar de constructor.
Vervolgens genereren we een |go| functie. Dit is een toepassing van de Static
Argument Transformation (zie \TODO{Cite SAT}).

\begin{spec}
foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldTree leaf branch = go
  where
    go (Leaf x)    = leaf x
    go (Node x y)  = branch (go x) (go y)

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
van de oneven nummers in een lijst berekent:

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

De eerste versie is echter effici\"enter: deze berkent rechtstreeks het
resultaat (een |Int|), terwijl de tweede versie twee tijdelijke |[Int]| lijsten
aanmaakt: een eerste als resultaat van |filter odd|, en een tweede als resultaat
van |map (^ 2)|.

In de ideale situatie willen we dus de effici\"entie van de eerste versie
combineren met de leesbaarheid van de tweede versie. Dit wordt mogelijk gemaakt
door \emph{fusion} \cite{wadler1990} \cite{gill1993}.

We kunnen fusion best uitleggen aan de hand van een eenvoudig voorbeeld:
\emph{map/map-fusion}. Dit is een transformatie die gegeven wordt door stelling
\ref{theorem:map-map-fusion}.

\newtheorem{theorem:map-map-fusion}{Stelling}[section]
\begin{theorem:map-map-fusion}\label{theorem:map-map-fusion}
\[ |map f . map g| ~~ |==| ~~ |map (f . g)| \]
\end{theorem:map-map-fusion}

\begin{proof}
Deze equivalentie is eenvoudig te bewijzen via inductie.  We bewijzen dit eerst
voor de lege lijst |[]|. Voor |map f . map g| krijgen we:

\begin{spec}
    map f (map g [])

== {- def |map []| -}

    map f []

== {- def |map []| -}

    []

== {- def |map []| -}

    map (f . g) []
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

Ter illustratie, als we bijvoorbeeld enkel de twee functies |map| en |filter|
beschouwen, hebben al vier rules nodig, en een bijkomende hulpfunctie
|mapFilter|:

\begin{spec}
map f . map g        == map (f . g)
map f . filter g     == mapFilter f g
filter f . map g     == filter (f . g)
filter f . filter g  == filter (\x -> f x && g x)

mapFilter :: (a -> b) -> (a -> Bool) -> [a] -> [b]
mapFilter _ _ []  = []
mapFilter f g (x : xs)
    | g x         = f x : mapFilter f g xs
    | otherwise   = mapFilter f g xs
\end{spec}

Maar als we nu een langere expressie |map f . map g . filter h| hebben, kunnen
we iets krijgen als |map f . mapFilter g h|, en dienen we weer nieuwe
fusion-regels toe te voegen om deze expressie te kunnen fusen. Het aantal nodige
regels stijgt dus zeer snel.

Voor sommige modules ligt het aantal hogere-orde functies erg hoog, dus wordt
deze aanpak onhaalbaar.

\subsection{Foldr/build-fusion}

Dit probleem wordt opgelost met \emph{foldr/build-fusion}. We kunnen |foldr|
beschouwen als een algemene manier om lijsten te \emph{consumeren}. Hiervan is
|build| de tegenhanger: een algemene manier om lijsten te \emph{produceren}.

\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}

We kunnen nu bijvoorbeeld |map| en |filter| met behulp van |build| defini\"eren:

\begin{spec}
map :: (a -> b) -> [a] -> [b]
map f ls = build $ \cons nil ->
    foldr (\x xs -> cons (f x) xs) nil ls

filter :: (a -> Bool) -> [a] -> [a]
filter f ls = build $ \cons nil ->
    foldr (\x xs -> if f x then cons x xs else xs) nil ls
\end{spec}

Het nut van |build| wordt nu duidelijk: we gebruiken deze functie om te
\emph{abstraheren} over de concrete constructoren: in plaats van |(:)| en |[]|
gebruiken we nu de abstracte |cons| en |nil| parameters.

De type-signatuur van |build| met het expliciet universeel gekwantificeerde type
|b| is cruciaal. Stel dat dit niet het geval zou zijn, en dat we |build| zouden
defini\"eren met de meest algemene type-signatuur:

\begin{code}
build' :: ((a -> [a] -> [a]) -> [a] -> t) -> t
build' g = g (:) []
\end{code}

Dan zou code als |list123| well-typed zijn:

\begin{code}
list123 :: [Int]
list123 = build' $ \cons nil -> 1 : cons 2 (cons 3 [])
\end{code}

We krijgen een lijst die zowel gebruikt maakt van de concrete constructoren als
de abstracte versies. Dit leidt tot problemen: intu\"itief laten de abstracte
versies ons toe om de constructoren |(:)| en |[]| te \emph{vervangen} door
andere functies -- en zoals we in Sectie \ref{section:universal-fold} zagen,
kunnen we het toepassen van |foldr| net beschouwen als het vervangen van de
constructoren door de argumenten van |foldr|!

Als we echter ook nog letterlijk verwijzen naar |(:)| en |[]|, is deze
vervanging onmogelijk. Het universeel gekwantificeerde type |b| lost dit
probleem op. De programmeur is verplicht een |g| mee te geven die werkt voor
\emph{elke} |b|, en hij weet niet welk type uiteindelijk geconstrueerd zal
worden. Bijgevolg en kan hij dus ook geen concrete constructoren gebruiken.

Nu we vastgesteld hebben dat enkel de abstracte versies van de constructoren
gebruikt worden, laat dit idee ons toe om de productie en consumatie van een
lijst te fusen, zodanig dat er geen tijdelijke lijst moet worden aangemaakt. We
werken dit nu formeel uit.

\newtheorem{theorem:foldr-build-fusion}{Stelling}[section]
\begin{theorem:foldr-build-fusion}\label{theorem:foldr-build-fusion}
Als

\[ |g :: forall b. (A -> b -> b) -> b -> b| \]

dan

\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]
\end{theorem:foldr-build-fusion}

\begin{proof} Van het type van een polymorfe functie kan een \emph{gratis
theorie} afgeleid worden \cite{wadler1989}. Zo krijgen we voor |g| dat voor alle
|f1|, |f2| en |h| met als types:

\begin{center}
\begin{spec}
h   :: B1 -> B2
f1  :: A -> B1 -> B1
f2  :: A -> B2 -> B2
\end{spec}
\end{center}

de volgende implicatie geldt:

\begin{align*}
(|forall x xs1 xs2. h xs1 == xs2| &\Rightarrow
        |h (f1 x xs1) == f2 x xs2|) \Rightarrow \\
(|forall xs1 xs2. h xs1 == xs2| &\Rightarrow
        |h (g f1 xs1) == g f2 xs2|)
\end{align*}

De gelijkheid |h xs1 == xs2| kunnen we tweemaal substitueren, waardoor de
implicatie herleid wordt tot:

\begin{align*}
(|forall x xs2. h (f1 x xs1)| & |== f2 x (h xs1)|) \Rightarrow \\
(|forall xs2. h (g f1 xs1)|   & |== g f2 (h xs1)|)
\end{align*}

We kunnen deze implicatie nu instanti\"eren met: |f1 := (:)|, |f2 := cons|, en
|h := foldr cons nil|. We krijgen dus:

\begin{align*}
(|forall x xs2. foldr cons nil (x : xs1)|  & |== cons x (foldr cons nil xs1)|)
    \Rightarrow \\
(|forall xs2. foldr cons nil (g (:) xs1)|  & |== g cons (foldr cons nil xs1)|)
\end{align*}

De linkerkant van de implicatie is triviaal geldig: dit is gewoon de definitie
van |foldr| voor een niet-ledige lijst. Hieruit volgt dat:

\[ |(forall xs2. foldr cons nil (g (:) xs2) == g cons (foldr cons nil xs2))| \]

Deze gelijkheid kunnen we opnieuw instanti\"eren, ditmaal met |xs2 := []|. Zo
krijgen we:

\begin{center}
\begin{spec}
    foldr cons nil (g (:) []) == g cons (foldr cons nil [])

== {- def |foldr []| -}

    foldr cons nil (g (:) []) == g cons nil

== {- def |build| -}

    foldr cons nil (build g) == g cons nil
\end{spec}
\end{center}

\end{proof}

Ter illustratie tonen we nu hoe met deze enkele fusion-regel onze elegantere
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

Uiteindelijk is |sumOfSquaredOdds'| dus volledig gereduceerd tot \'e\'en enkele
|foldr| over een lijst: het is niet meer nodig om tijdelijke lijsten te
alloceren om het resultaat te berekenen. In \TODO{Cite results chapter} tonen we
aan dat dit leidt tot significante versnellingen.

We krijgen dus als het ware het beste van beide werelden: we kunnen elegante
definities gebruiken voor de functies, die eenvoudiger leesbaar zijn en
makkelijker onderhoudbaar; maar tevens worden deze vertaald door de compiler tot
snelle, geoptimaliseerde versies.

\subsection{Foldr/build voor algebra\"ische datatypes}

In Sectie \ref{section:universal-fold} toonden we aan dat we een |fold| kunnen
defini\"eren voor om het even welk algebra\"isch datatype. Dit is ook mogelijk
voor |build|. Beschouw bijvoorbeeld een |build| voor ons |Tree|-datatype:

\begin{code}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = g Leaf Branch
\end{code}

Zodra we beschikken over een |fold| en een |build| voor een algebra\"isch
datatype, is het mogelijk om fusion toe te passen. Voor het type |Tree| wordt de
fusion-regel gegeven in definitie \ref{theorem:foldr-build-tree-fusion}.

\newtheorem{theorem:foldr-build-tree-fusion}{Definitie}[section]
\begin{theorem:foldr-build-tree-fusion}\label{theorem:foldr-build-tree-fusion}
\[ |foldTree leaf branch (buildTree g)| ~~ |==| ~~ |g leaf branch| \]
\end{theorem:foldr-build-tree-fusion}

Het bewijs hiervan verloopt analoog aan het bewijs voor
\ref{theorem:foldr-build-fusion} en wordt hier achterwege gelaten \TODO{Of moet
ik dit wel includeren? Het is 99\% hetzelfde...}.

Om dit te verduidelijken kunnen we kijken naar een concreet voorbeeld. Beschouw
de voorbeeldfunctie |treeUpTo| die een boom maakt met alle elementen van |n| tot
en met |m| in-order in de bladeren.

\begin{code}
treeUpTo :: Int -> Int -> Tree Int
treeUpTo n m = buildTree $ \leaf branch ->
    let g lo hi
            | lo >= hi   = leaf lo
            | otherwise  =
                let mid = (lo + hi) `div` 2
                in branch (g lo mid) (g (mid + 1) hi)
    in g n m
\end{code}

Nu kunnen we bestuderen wat er door fusie gebeurt met een expressie als |sumTree
(treeUpTo n m)|, die een tijdelijke boom aanmaakt.

\begin{spec}
    sumTree (treeUpTo n m)

== {- inline |sumTree| -}

    foldTree id (+) (treeUpTo n m)

== {- inline |makeTree| -}

    foldTree id (+) (buildTree $ \leaf branch ->
        let g lo hi
                | lo >= hi   = leaf lo
                | otherwise  =
                    let mid = (lo + hi) `div` 2
                    in branch (g lo mid) (g (mid + 1) hi)
        in g n m)

== {- foldTree/buildTree-fusion -}

    (\leaf branch ->
        let g lo hi
                | lo >= hi   = leaf lo
                | otherwise  =
                    let mid = (lo + hi) `div` 2
                    in branch (g lo mid) (g (mid + 1) hi)
        in g n m)
    id (+)

== {- $\beta$-reductie -}

    let g lo hi
            | lo >= hi   = id lo
            | otherwise  =
                let mid = (lo + hi) `div` 2
                in (g lo mid) + (g (mid + 1) hi)
    in g n m
\end{spec}

We krijgen een expressie die rechtstreeks de som uitrekent zonder ooit een
constructor te gebruiken. Opnieuw zal dit voor een significante versnelling
zorgen \TODO{Cite results chapter}.

Omdat naast |fold| ook |build| functies eenvoudig af te leiden zijn vanuit de
definitie van een datatype, hebben we dit ook geautomatiseerd. De programmeur
dient enkel nog |deriveBuild| op te roepen:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveBuild quote Tree "buildTree")
\end{spec}
%}

Het algoritme om een |build| te genereren werkt als volgt:

\begin{enumerate}

\item De fold gebruikt een universeel gekwantificeerd type |b| in een functie
|g| en geeft een waarde terug van het opgegeven type.

\begin{spec}
buildTree :: (forall b. ... -> b) -> Tree a
buildTree g = elapsed

buildList  :: (forall b. ... -> b) -> [a]
buildList g = elapsed
\end{spec}

\item Opnieuw krijgen we voor elke constructor een functieparameter, ditmaal
voor |g|. De types voor deze functieparameters worden afgeleid op dezelfde
manier als in het algoritme voor |deriveFold| (zie Sectie
\ref{section:universal-fold}).

\begin{spec}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = elapsed

buildList  :: (forall b. (a -> b -> b) -> b -> b) -> [a]
buildList g = elapsed
\end{spec}

\item De implementatie bestaat vervolgens uit het toepassen van |g| op de
concrete constructoren.

\begin{spec}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = g Leaf Branch

buildList  :: (forall b. (a -> b -> b) -> b -> b) -> [a]
buildList g = g (:) []
\end{spec}

\end{enumerate}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie folds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie builds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Implementatie \& evaluatie}

\section{GHC Core}

Eerder beschreven we al \TODO{backreference} dat we voor deze thesis werken met
GHC \cite{ghc}, de de-facto standaard Haskell compiler.

GHC werkt met een \emph{kerneltaal}. Een kerneltaal is een sterk gereduceerd
subset van de programmeertaal (in dit geval Haskell). Het is natuurlijk wel
mogelijk om elk Haskell-programma uit te drukken in de kerneltaal, al is dit
meestal veel minder beknopt.

De compiler zet na het parsen het programma om naar een equivalent programma in
deze kerneltaal. Dit proces heet \emph{desugaring}.

Het gebruik van een dergelijke kerneltaal heeft verschillende voordelen:

\begin{itemize}[topsep=0.00cm]

\item De syntax van de kerneltaal is zeer eenvoudig. Hierdoor kunnen de
programmeur en de compiler op een simpelere manier redeneren over expressies,
zonder rekening te houden met op dat moment oninteressante syntactische details.

\item Om nieuwe syntax toe te voegen, dient men enkel het
\emph{desugaring}-proces aan te passen en hoeft men geen aanpassingen te doen in
de rest van de compiler.

\item Verschillende programmeertalen kunnen dezelfde kerneltaal delen. Dit laat
toe om bepaalde tools en optimalisaties \'e\'enmaal te schrijven en vervolgens
toe te passen voor programmas geschreven in verschillende programmeertalen. Dit
voordeel is echter niet van toepassing voor GHC, omdat deze een eigen kerneltaal
gebruikt.

\end{itemize}

De kerneltaal van Haskell heet GHC Core \cite{tolmach2009}.

Om onze fold- en build-detectie te implementeren hebben we dus twee keuzes. We
kunnen ofwel de Haskell-code direct manipuleren. Er bestaan reeds verschillende
libraries om deze taak eenvoudiger te maken, zoals bijvoorbeeld
\emph{haskell-src-exts} \cite{haskell-src-exts}.

We kunnen echter ook werken met de GHC Core. Dit heeft voor ons een groot aandal
voordelen.

\begin{itemize}[topsep=0.00cm]

\item Zoals we eerder al vermeldden, is het expressietype veel eenvoudiger. Ter
illustratie: het |Expr|-type dat in \emph{haskell-src-exts} gebruikt wordt heeft
46 verschillende constructoren, terwijl het |Expr|-type van GHC Core er slechts
10 heeft.

\item De GHC Core gaat door verschillende optimalisatie-passes. Veel van deze
passes vereenvoudigen de expressies, wat op zijn beurt de analyse weer vooruit
helpt. Beschouw bijvoorbeeld de volgende functie |jibble|:

\begin{code}
jibble :: [Int] -> Int
jibble []        = 1
jibble (x : xs)  = wiggle x xs

wiggle :: Int -> [Int] -> Int
wiggle x xs = x * jibble xs + 1
\end{code}

Hier is het praktisch onhaalbaar om een |foldr|-patroon te herkennen door het
gebruik van de hulpfunctie |wiggle|. Maar, eens deze functie ge-inlined is,
krijgen we de functie:

\begin{spec}
jibble :: [Int] -> Int
jibble []        = 1
jibble (x : xs)  = x * jibble xs + 1
\end{spec}

Onze detector kan de laatste versie onmiddelijk herkennen.

\item Tenslotte beschikken we ook over type-informatie: de GHC API laat ons toe
types van onder meer variabelen en functies op te vragen. Dit is in principe
niet essentieel voor onze detector, maar kan wel zeer nuttig zijn. Beschouw
bijvoorbeeld:

\begin{code}
add :: Int -> Int -> Int
add x y = elapsed
\end{code}

We kunnen, zonder de definitie van |add| te bekijken, al uit de type-signatuur
opmaken dat |add| geen |fold| noch |build| zal zijn. Het is immers niet mogelijk
te folden over een |Int| of er \'e\'en aan te maken met build: |Int| valt niet
in de klasse van de algebra\"ische datatypes.

\end{itemize}

We dienen wel op te merken dat er ook een belangrijk gekoppeld is aan het werken
met GHC Core in plaats van Haskell code. Het wordt namelijk veel moeilijker om
de resultaten van onze analyse te gebruiken voor \emph{refactoren}: in dit
geval, de originele Haskell code te herschrijven als toepassing van een |fold|
of |build|. Als we dit willen mogelijk maken, zouden we een soort geannoteerd
expressie-type nodig hebben, zodanig dat we de expressies in GHC Core kunnen
terugkoppelen aan Haskell-expresssies. Wanneer we dan de GHC Core expressies
automatisch herschrijven, moet de Haskell code ook geupdate worden. Dit zou ons
echter te ver voeren.

Om bovenstaande redenen kiezen we er dus voor om met GHC Core te werken. In
Figuur \ref{figure:haskell-to-ghc-core} geven we een kort overzicht van hoe
Haskell-expressies worden omgezet naar GHC Core-expressies.

\begin{figure}[h]
  \begin{tabular}{ll}
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    "Jan"
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    ((:) 'J' ((:) 'a' ((:) 'n' )))
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    head []       = undefined
    head (x : _)  = x
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    head = \xs -> case xs of
        []       -> undefined
        (:) x _  -> x
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    let  x  = 3
         y  = 4
    in x + y + z
    where z = 5
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    let z = 5
    in  let x = 3
        in  let y = 4
            in (+) x ((+) y z)
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    compare a b
      | a > b      = GT
      | a == b     = EQ
      | otherwise  = LT
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    compare = \a -> \b ->
      case (>) a b of
        True   -> GT
        False  -> case (==) a b of
          True   -> EQ
          False  -> LT
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    foldM f a []        = return a
    foldM f a (x : xs)  = do
      a' <- f a x
      foldM f a' xs
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    foldM = \f a ls -> case ls of
      []        -> return a
      (:) x xs  ->
        f a x >>= \a' -> foldM f a' xs
    \end{spec}
    \end{minipage} \\
  \end{tabular}
  \caption{Een overzicht van hoe Haskell-expressies worden omgezet naar
  GHC Core-expressies. Links ziet u de Haskell-expressies, en rechts de
  overeenkomstige GHC Core-expressies}
  \label{figure:haskell-to-ghc-core}
\end{figure}

\section{Het GHC Plugins systeem}

De vraag is nu hoe we deze GHC Core kunnen manipuleren. Tot recentelijk was dit
enkel mogelijk door de source code van GHC direct aan te passen. Gelukkig werd
in GHC 7.2.1 een nieuw plugin systeem ge\"introduceerd \cite{ghc-plugins} dat
dit sterk vereenvoudigd.

Meer bepaald is het nu mogelijk om Core-naar-Core tranformaties te implementeren
in aparte modules, en deze vervolgens mee te geven aan GHC via commmand-line
argumenten.

De module moet een |plugin :: Plugin| definitie bevatten.

\begin{code}
plugin :: Plugin
plugin = defaultPlugin {installCoreToDos = install}
\end{code}

De |installCoreToDos| laat toe om de lijst van passes aan te passen. Dit is een
standaard Haskell-lijst en bevat initi\"eel alle passes die GHC traditioneel
uitvoert. Met |intersperse| kunnen we bijvoorbeeld onze pass laten uitvoeren
tussen elke twee GHC-passes.

\begin{code}
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _options passes = return $ intersperse myPlugin passes
  where
    myPlugin = CoreDoPluginPass "My plugin" (bindsOnlyPass myPass)
\end{code}

De implementatie van de effectieve pass heeft typisch de type-signatuur
|CoreProgram -> CoreM CoreProgram|. Hierin kunnen we dus gemakkelijk de
expressies bewerken: deze worden voorgesteld als een algebra\"isch datatype.

\begin{code}
myPass :: CoreProgram -> CoreM CoreProgram
myPass = elapsed
\end{code}

We illustreren hier een vereenvoudigde versie van het algebra\"isch datatype dat
door GHC gebruikt wordt:

\begin{spec}
type CoreProgram = [Bind Var]

data Bind b
    =  NonRec b Expr
    |  Rec [(b, Expr)]

data Expr b
    =  Var Id
    |  Lit Literal
    |  App (Expr b) (Expr b)
    |  Lam b (Expr b)
    |  Let (Bind b) (Expr b)
    |  Case (Expr b) b Type [Alt b]
    |  Cast (Expr b) Coercion
    |  Tick (Tickish Id) (Expr b)
    |  Type Type
    |  Coercion Coercion

type Alt b = (AltCon, [Id], Expr b)
\end{spec}

|Var| stelt eenvoudigweg variabelen voor, en literals worden door |Lit|
geconstrueerd. |App| en |Lam| zijn lambda-applicatie en lambda-abstractie
respectievelijk, concepten waarmee we bekend zijn uit de lambda-calculus. |Let|
stelt |let|-expressies voor, zowel recursief als niet-recursief. |Case| stelt
|case|-expressies voor maar heeft meerdere parameters: een extra binder voor de
expressie die onderzocht wordt door de |case|-expressie (ook de \emph{scrutinee}
genoemd), en het type van de resulterende alternatieven. |Cast|, |Tick|, |Type|
en |Coercion| worden gebruikt voor expressies die weinig relevantie hebben met
deze thesis. We vermelden deze dus zonder verdere uitleg.

Haskell-programma's worden dus door de compiler voorgesteld in deze abstracte
syntaxboom, en plugins kunnen deze bomen naar willekeur transformeren. Figuur
\ref{figure:ghc-core-ast} toont hoe GHC-Core expressies eruitzien in deze
syntaxboom.

\begin{figure}[h]
  \begin{tabular}{ll}
    |x| \hspace{0.40\textwidth} &
    |Var "x"| \\

    |2| &
    |Lit 2| \\

    |e1 e2| &
    |App e1 e2| \\

    |\x -> e| &
    |Lam x e| \\

    |let x = e1 in e2| &
    |Let (NonRec x e1) e2| \\

    |case e1 of C x1 x2 -> e2| &
    |Case e1 _ _ [(DataCon C, [x1, x2], e2)]| \\
  \end{tabular}
  \caption{Een overzicht van hoe GHC-Core expressies worden voorgesteld in de
  abstracte syntaxboom.}
  \label{figure:ghc-core-ast}
\end{figure}

Ter illustratie geven we hier een kleine pass die niet-recursieve binds inlined,
dit is, |let x = e1 in e2| omzet naar |subst e2 x e1|.

\begin{code}
simpleBetaReduction :: [Bind Var] -> [Bind Var]
simpleBetaReduction = map (goBind [])
  where
    goBind :: [(Var, Expr Var)] -> Bind Var -> Bind Var
    goBind env (NonRec x e)  = NonRec x (go ((x, e) : env) e)
    goBind env (Rec bs)      = Rec [(x, go env e) | (x, e) <- bs]

    go :: [(Var, Expr Var)] -> Expr Var -> Expr Var
    go env (Var x)                 =
        case lookup x env of Nothing -> Var x; Just e -> e
    go env (Lit x)                 = Lit x
    go env (App e1 e2)             = App (go env e1) (go env e2)
    go env (Lam x e)               = Lam x (go env e)
    go env (Let (NonRec x e1) e2)  = go ((x, e1) : env) e2
    go env (Let (Rec bs) e2)       =
        Let (Rec [(x, go env e1) | (x, e1) <- bs]) (go env e2)
    go env (Case e1 x1 ty alts)    =
        Case (go env e1) x1 ty
            [(ac, bnds, go env e2) | (ac, bnds, e2) <- alts]
    go env (Cast e c)              = Cast (go env e) c
    go env (Tick t e)              = Tick t (go env e)
    go env (Type t)                = Type t
    go env (Coercion c)            = Coercion c
\end{code}

E\'ens een dergelijke plugin geschreven is, kan deze eenvoudig gebruikt worden.
De code dient \emph{gepackaged} te worden met \emph{cabal} \cite{cabal} en
vervolgens kan men deze plugin installeren:

\begin{lstlisting}
cabal install my-plugin
\end{lstlisting}

Men kan nu door slechts enkele commandolijn-argumenten mee te geven GHC opdragen
dat deze plugin geladen en uitgevoerd moet worden tijdens de compilatie:

\begin{lstlisting}
ghc --make -package my-plugin -fplugin MyPlugin test.hs
\end{lstlisting}

Waarbij |MyPlugin| de naam van de module is die |plugin :: Plugin| bevat, en
\texttt{my-plugin} de naam van het ge\"installeerde cabal-package. We kunnen dus
concluderen dat met dit systeem het zeer eenvoudig is om GHC uit te breiden of
te wijzigen, zonder dat de code van GHC moet aangepast worden.


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
