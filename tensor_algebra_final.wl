(* ::Package:: *)

(*Generate the identity tensor IdentityTensor[d,n] produces the identity tensor in d dimensions of level n*)
ClearAll[IdentityTensor];
IdentityTensor[n_Integer]:=Join[{1},Table[ConstantArray[0,ConstantArray[2,i]],{i,1,n}]];
IdentityTensor[d_Integer,n_Integer]:=Join[{1},Table[ConstantArray[0,ConstantArray[d,i]],{i,1,n}]];
IdentityTensor[a_List]:=Join[{1},Table[ConstantArray[0,ConstantArray[Length[a[[2]]],i]],{i,1,Length[a]-1}]];

(*Generate the zero tensor IdentityTensor[d,n] produces the zero tensor in d dimensions of level n*)
ClearAll[ZeroTensor];
ZeroTensor[n_Integer]:=Join[{0},Table[ConstantArray[0,ConstantArray[2,i]],{i,1,n}]];
ZeroTensor[d_Integer,n_Integer]:=Join[{0},Table[ConstantArray[0,ConstantArray[d,i]],{i,1,n}]];
ZeroTensor[a_List]:=Join[{0},Table[ConstantArray[0,ConstantArray[Length[a[[2]]],i]],{i,1,Length[a]-1}]];
AllZeros[l_]:=If[l[[0]]==List,If[Apply[Plus,Abs[Flatten[l]]]==0,True,False],False]

ClearAll[RaggedListShape];
RaggedListShape[ragged_?ListQ]:=Table[Dimensions[i],{i,ragged}]

ClearAll[QTensor];
QTensor[tensor_]:=If[And[ListQ[tensor],Min[RaggedListShape[tensor]]==Max[RaggedListShape[tensor]]],True,False]

ClearAll[TensorShape];
TensorShape[tensor_?QTensor]:=Join[{1},RaggedListShape[tensor[[2;;]]]]

(*Redefines the built in Mathematica tensor so as to fix for strange errors*)
ClearAll[TensorProductNew];
TensorProductNew[a_?TensorQ,b_?TensorQ]:=Outer[Times,a,b]
TensorProductNew[a_,b_?PossibleZeroQ]:=a-a
TensorProductNew[a_?PossibleZeroQ,b_]:=b-b
TensorProductNew[a_?TensorQ,b_?Internal`RealValuedNumberQ]:=TensorProduct[a,b]
TensorProductNew[a_?Internal`RealValuedNumberQ,b_?TensorQ]:=TensorProduct[a,b]
TensorProductNew[a_?Internal`RealValuedNumberQ,b_?Internal`RealValuedNumberQ]:=a*b
TensorProductNew[a_?AllZeros,b_?Internal`RealValuedNumberQ]:=a
TensorProductNew[a_?Internal`RealValuedNumberQ,b_?AllZeros]:=b


(*TensorAlgebraProduct[t1,t2] produces the tensor product between the two tensors t1 and t2*)
TensorAlgebraProduct[tensor1_,tensor2_]:=Table[Sum[TensorProductNew[tensor1[[i]],tensor2[[k+1-i]]],{i,1,k}],{k,1,Length[tensor1]}]
TensorAlgebraProduct[tensor1_?QTensor,tensor2_?Internal`RealValuedNumberQ]:=Times[tensor1,tensor2]
TensorAlgebraProduct[tensor1_?Internal`RealValuedNumberQ,tensor2_?QTensor]:=Times[tensor1,tensor2]

TensorAlgebraProductParallel[tensor1_?QTensor,tensor2_?QTensor]:=Module[{n,tensor3},
	n = Length[tensor1];
	tensor3 = ParallelTable[Sum[TensorProductNew[tensor1[[i]],tensor2[[k+1-i]]],{i,1,k}],{k,1,n}]]
	
TensorAlgebraIdentity[a_]:=Apply[Plus,Table[TensorAlgebraPower[IdentityTensor[a]-a,n],{n,0,Length[a]+2}]]
	
(*Generates a list of all the tensor powers of the tensor t up to and including the nth power*)
TensorAlgebraPowerList[a_,n_]:=Module[{powers},
	powers=ConstantArray[0,n];
	powers[[1]]=a;
	For[i=2,i<=n,i++,powers[[i]]=TensorAlgebraProduct[powers[[i-1]],powers[[1]]]];
	powers]

(*Computes the nth power of the tensor t*)
TensorAlgebraPower[a_,n_?PossibleZeroQ]:=IdentityTensor[a]
TensorAlgebraPower[a_,n_]:=Last[TensorAlgebraPowerList[a,n]]

ClearAll[TensorAlgebraPlus];
TensorAlgebraPlus[a_?Internal`RealValuedNumberQ,b_?ListQ]:=a*IdentityTensor[b]+b
TensorAlgebraPlus[a_?ListQ,b_?Internal`RealValuedNumberQ]:=TensorAlgebraPlus[b,a]
TensorAlgebraPlus[a_?ListQ,b_?ListQ]:=a+b
TensorAlgebraPlus[a_?Internal`RealValuedNumberQ,b_?Internal`RealValuedNumberQ]:=a+b

(*Checks to see value of first element*)
FirstZero[a_]:=If[a[[1]]==0,True,False]
FirstOne[a_]:=If[a[[1]]==1,True,False]

(*Computes the Logarithm of a tensor*)
ClearAll[TensorLogarithm];
TensorLogarithm::badargs="The input tensor must be an element of the space: 1+\!\(\*SuperscriptBox[StyleBox[\"t\",FontWeight->\"Bold\"],
	StyleBox[\"N\",FontSlant->\"Italic\"]]\)(\!\(\*SuperscriptBox[\(\[DoubleStruckCapitalR]\), \(d\)]\)), i.e. the first element must be equal to 1";
TensorLogarithm::badtensor="The input tensor was an element of \!\(\*SuperscriptBox[StyleBox[\"t\",FontWeight->\"Bold\"],
	StyleBox[\"N\",FontSlant->\"Italic\"]]\)(\!\(\*SuperscriptBox[\(\[DoubleStruckCapitalR]\), \(d\)]\)) and not 1+\!\(\*SuperscriptBox[StyleBox[\"t\",FontWeight->\"Bold\"],
		StyleBox[\"N\",FontSlant->\"Italic\"]]\)(\!\(\*SuperscriptBox[\(\[DoubleStruckCapitalR]\), \(d\)]\)) as expected. The result shown is for the input tensor with the first zero changed to a 1";
TensorLogarithm[a_?FirstOne]:=Module[{n,powers},
	n=Length[a];
	powers=TensorAlgebraPowerList[a-IdentityTensor[n-1],n];
	Apply[Plus,Table[(-1)^(k+1)/k powers[[k]],{k,1,n}]]]
TensorLogarithm[a_?FirstZero]:=(Message[TensorLogarithm::badtensor];Module[{n,powers},
	n=Length[a];
	powers=TensorAlgebraPowerList[a,n];
	Apply[Plus,Table[(-1)^(k+1)/k powers[[k]],{k,1,n}]]])
TensorLogarithm[args___]:="nothing"/;Message[TensorLogarithm::badargs]

(*Inverse of TensorLogarithm*)
ClearAll[TensorExponential];
TensorExponential::badargs="The input tensor must be an element of the space: \!\(\*SuperscriptBox[StyleBox[\"t\",FontWeight->\"Bold\"],
	StyleBox[\"N\",FontSlant->\"Italic\"]]\)(\!\(\*SuperscriptBox[\(\[DoubleStruckCapitalR]\), \(d\)]\)), i.e. the first element must be equal to 0";
TensorExponential[a_?FirstZero]:=Module[{n,powers},
	n=Length[a];
	powers=TensorAlgebraPowerList[a,n];
	IdentityTensor[n-1]+Apply[Plus,Table[1/k! powers[[k]],{k,1,n}]]];
TensorExponential[args___]:="nothing"/;Message[TensorExponential::badargs]


(* WRITTEN WITH JEREMY
If p is a d-dimensional path given as a list of points,where each point is a list of
d numbers,and m is a positive integer,then Sig[p,m] is the signature of p up to level
m excluding the initial 1,given as a list of nestedlists.*)
Sig[p_,m_]:=Module[{StraightSig,Chen},
	StraightSig[displacement_]:=FoldList[Outer[Times,displacement/#2,#1]&,displacement,Range[2,m]];
	Chen[d1_,d2_]:=Join[{d1[[1]]+d2[[1]]},Table[d1[[level]]+d2[[level]]+
		Apply[Plus,MapThread[Outer[Times,#1,#2]&,{Take[d1,level-1],
			Reverse[Take[d2,level-1]]}]],{level,2,m}]];
	Prepend[Fold[Chen,StraightSig/@Differences[p]],1]]


(*LogSig[p,m] is the expanded log signature of p up to level m.*)
LogSig[p_,m_]:=TensorLogarithm[Sig[p,m]]


(*Tools for free Lie algebra basis calculations.
  Code here is based upon code by Jeremy but has been expanded by myself to generate symbolic results. *)

(* Find the length of a bracked expression, e.g. {e1,{e2,e3}} *)
LengthOfExpression[a_Integer]:=1;
LengthOfExpression[a_Symbol]:=IntegerLength[ToExpression[StringTake[SymbolName[a],-(StringLength[SymbolName[a]]-1)]]];
LengthOfExpression[{a_,b_}]:=LengthOfExpression[a]+LengthOfExpression[b];

(* Used to compute a Hall Basis *)
GenerateHallBasisSymbolic[d_Integer, 1, less_]:={Symbol["e"<> ToString[#]]&/@Range[d]}
GenerateHallBasisSymbolic[d_Integer, m_Integer, less_]:=
 With[{known = GenerateHallBasisSymbolic[d,m - 1,less]}, 
  With[{new = 
     Table[Join @@ 
       Table[If[And[less[x,y],
         Or[IntegerQ[x], Not[ListQ[x]], Not[less[x[[2]], y]]]], {x, y}, 
         Nothing], {x, known[[firstLev]]}, {y, 
         known[[m - firstLev]]}], {firstLev, 1, m-1}]},
    Append[known,Join@@new]]];

(* Reverse all the brackets in a bracketed expression *)
ReverseAllBrackets[a_Integer]:=a;
ReverseAllBrackets[a_Symbol]:=a;
ReverseAllBrackets[{a_,b_}]:={ReverseAllBrackets[b],ReverseAllBrackets[a]};

(* Code to compare two symbols, i.e. e1 and e2. Note that we define e1 to be less than e2 *)
SymbolLessThan[a_Integer,b_Integer]:=LessThan[b][a];
SymbolLessThan[a_Symbol,b_Symbol]:=LessThan[ToExpression[StringTake[SymbolName[b],
 -(StringLength[SymbolName[b]]-1)]]][ToExpression[StringTake[SymbolName[a],
  -(StringLength[SymbolName[a]]-1)]]];

(* Define the relationship between bracketed expressions, needed to compute the Hall basis *)
LessExpressionStandardHall[a_, b_] := 
 With[{ll = LengthOfExpression[a], lr = LengthOfExpression[b]}, 
  If[ll == lr, 
   If[Or[ll == 1,And[Not[ListQ[a]],Not[IntegerQ[a]]]], SymbolLessThan[b,a], 
    If[LessExpressionStandardHall[a[[1]], b[[1]]], True, 
     If[LessExpressionStandardHall[b[[1]], a[[1]]], False, 
      LessExpressionStandardHall[a[[2]], b[[2]]]]]], SymbolLessThan[lr,ll]]];
  
(* Obtain the symbolic Hall basis *)
GenerateStandardHallBasisSymbolic[d_Integer,m_Integer] := 
  Map[ReverseAllBrackets, GenerateHallBasisSymbolic[d,m,LessExpressionStandardHall],{2}];


ExpandBracketedExp[x_Integer,d_Integer] := 
 Join[ConstantArray[0, x - 1], {1}, ConstantArray[0, d - x]]; 
ExpandBracketedExp[{x_,y_},d_Integer] :=
 With[{a = ExpandBracketedExp[x,d], b = ExpandBracketedExp[y,d]}, 
  TensorProduct[a, b] - TensorProduct[b, a]];

ClearAll[ExpandBracketedExpSymbolic];
ExpandBracketedExpSymbolic[j_Integer,d_Integer]:=j;
ExpandBracketedExpSymbolic[j_,d_Integer]:=Module[{numeric},
 numeric=Map[FromDigits@StringDrop[SymbolName[#],1]&,j,{-1}];
  Apply[Plus,Table[Extract[ExpandBracketedExp[numeric,d],i]
   Symbol["e"<>ToString[FromDigits[Flatten[Table[IntegerDigits[k],
   {k,Flatten[i]}]]]]],{i,Tuples[Range[d],If[ListQ[numeric],
    Length[Flatten[numeric]],1]]}]]]

BasisTensorProduct[a_,b_]:=Module[{aNum,bNum},
 aNum=IntegerDigits[ToExpression[StringTake[SymbolName[a],-(StringLength[SymbolName[a]]-1)]]];
  bNum=IntegerDigits[ToExpression[StringTake[SymbolName[b],-(StringLength[SymbolName[b]]-1)]]];
   Symbol["e" <> ToString[FromDigits[Join[aNum,bNum]]]]
    ];
BasisTensorProduct[a_,(b_-c_)]:=BasisTensorProduct[a,b]-BasisTensorProduct[a,c];
BasisTensorProduct[(a_-b_),c_]:=BasisTensorProduct[a,c]-BasisTensorProduct[b,c];


ClearAll[ListToTensor];
ListToTensor[list_,d_:2,padding_:False]:=Module[{l,n,useList},
	l=Length[list];
	n=Round[N[-1+Log[1+(-1+d) l]/Log[d]]];
	useList=PadRight[list,(-1+d^(1+n))/(-1+d)];
	Join[{useList[[1]]},Table[ArrayReshape[useList[[(-1+d^i)/(-1+d)+1;;(-1+d^(1+i))/(-1+d)]],ConstantArray[d,i]],{i,1,n}]]
]


ClearAll[InverseTensor];
InverseTensor[a_]:=Apply[Plus,Prepend[TensorAlgebraPowerList[IdentityTensor[a]-a,Length[a]],IdentityTensor[a]]]

ClearAll[SymbolicTensorAlgebraProduct];
SymbolicTensorAlgebraProduct[a_,b_]:=Module[{pairs,level},
	pairs[k_]:=Flatten[Table[If[i+j==k,{i,j},Unevaluated[Sequence[]]],{i,0,Length[a]+1},{j,0,Length[a]+1}],1];
	level[k_]:=Apply[Plus,Table[TensorProduct[a[[thing[[1]]]],b[[thing[[2]]]]],{thing,pairs[k]+1}]];
	TensorExpand[Table[level[i],{i,0,Length[a]-1}]]
]

ClearAll[SymbolicTensorAlgebraIdentity];
SymbolicTensorAlgebraIdentity[a_]:=Prepend[ConstantArray[0,Length[a]-1],1]

ClearAll[SymbolicTensorAlgebraPowerList];
SymbolicTensorAlgebraPowerList[a_,n_,zero_:True]:=If[zero,Prepend[FoldList[SymbolicTensorAlgebraProduct,ConstantArray[a,n]],SymbolicTensorAlgebraIdentity[a]],FoldList[SymbolicTensorAlgebraProduct,ConstantArray[a,n]]]

ClearAll[SymbolicTensorAlgebraInverse];
SymbolicTensorAlgebraInverse[a_]:=(1/a[[1]])*Apply[Plus,SymbolicTensorAlgebraPowerList[(SymbolicTensorAlgebraIdentity[a]-a),Length[a]]]

ClearAll[SymbolicTensorAlgebraPower];
SymbolicTensorAlgebraPower[a_,n_]:=Last[SymbolicTensorAlgebraPowerList[a,n,False]]

ClearAll[SymbolicTensorAlgebraLog];
SymbolicTensorAlgebraLog[a_]:=Module[{powers},
	powers=SymbolicTensorAlgebraPowerList[a-SymbolicTensorAlgebraIdentity[a],Length[a],False];
	Apply[Plus,Table[(-1)^(i+1)*powers[[i]]/i,{i,1,Length[powers]}]]
]

ClearAll[SymbolicTensorAlgebraExp];
SymbolicTensorAlgebraExp[a_]:=Module[{powers},
	powers=SymbolicTensorAlgebraPowerList[a,Length[a]];
	Apply[Plus,Table[powers[[i]]/((i-1)!),{i,1,Length[powers]}]]
]


(*Very fast shuffle product of two lists of numbers
  Taken from here: https://mathematica.stackexchange.com/questions/41614/shuffle-product-of-two-lists *)
ShuffleW[s1_,s2_]:=Module[{p,tp,ord},p=Permutations@Join[1&/@s1,0&/@s2]\[Transpose];
 tp=BitXor[p,1];
  ord=Accumulate[p] p+(Accumulate[tp]+Length[s1]) tp;
   Outer[Part,{Join[s1,s2]},ord,1][[1]]\[Transpose]]

NotListQ[a_]:=Not[ListQ[a]];

(*Shuffle product of two basis elements*)
ClearAll[Shuffle];
Shuffle[a_,b_Integer]:=a*b;
Shuffle[a_Integer,b_]:=a*b;
Shuffle[a_?PossibleZeroQ,b_Symbol]:=b;
Shuffle[a_Symbol,b_?PossibleZeroQ]:=a;
Shuffle[a_Symbol,b_Symbol]:=Module[{aNum,bNum,shuffles},
 aNum=IntegerDigits[ToExpression[StringTake[SymbolName[a],-(StringLength[SymbolName[a]]-1)]]];
  bNum=IntegerDigits[ToExpression[StringTake[SymbolName[b],-(StringLength[SymbolName[b]]-1)]]];
   shuffles=ShuffleW[aNum,bNum];
   Apply[Plus,Symbol["e" <> ToString[FromDigits[#]]]&/@shuffles]
    ]
Shuffle[a_List,b_Symbol]:=Apply[Plus,Shuffle[#,b]&/@a];
Shuffle[a_Symbol,b_List]:=Shuffle[b,a];
Shuffle[a_List,b_?NotListQ]:=Shuffle[b,a];
Shuffle[a_List,b_List]:=Apply[Plus,Map[Shuffle[a,#]&,b]];
Shuffle[a_Plus,b_Symbol]:=Shuffle[ReplaceAll[Plus->List][a],b];
Shuffle[a_Symbol,b_Plus]:=Shuffle[b,a];
Shuffle[a_Plus,b_Plus]:=Shuffle[ReplaceAll[Plus->List][a],ReplaceAll[Plus->List][b]];
Shuffle[a_Plus,b_List]:=Shuffle[ReplaceAll[Plus->List][a],b];
Shuffle[a_List,b_Plus]:=Shuffle[b,a];
Shuffle[a_Times,b_]:=If[a[[1]]==-1,-Shuffle[a[[2]],b],If[a[[1]]<0,-Shuffle[ConstantArray[a[[2]],-a[[1]]],b],
 Shuffle[ConstantArray[a[[2]],a[[1]]],b]]];
Shuffle[a_,b_Times]:=Shuffle[b,a];

(* Gives degree of a Hall basis element *)
ClearAll[HallDegree];
HallDegree[a_Integer]:=0;
HallDegree[a_Symbol]:=IntegerLength[ToExpression[StringTake[SymbolName[a],-(StringLength[SymbolName[a]]-1)]]];
HallDegree[a_Times]:=HallDegree[a[[2]]];
HallDegree[a_List]:=Length[Flatten[a]];
HallDegree[a_Plus]:=Max[HallDegree/@ReplaceAll[Plus->List][a]]

(* Generates symbolic basis of tensor space *)
ClearAll[TensorBasis];
TensorBasis[d_,m_]:=Prepend[Symbol["e"<>ToString[#]]&/@FromDigits
 /@Flatten[Table[Tuples[Range[1,d],i],{i,1,m}],1],1];

ClearAll[BasisMonomials];
BasisMonomials[d_,m_,degree_:False]:=Module[{bases,tuples,monomials},
 bases=ExpandBracketedExpSymbolic[#,d]&/@Prepend[Flatten[GenerateStandardHallBasisSymbolic[d,m],1],1];  
  tuples=DeleteDuplicates[Table[If[Apply[Plus,Map[HallDegree,tuple]]<=m,tuple,Nothing[]],{tuple,Tuples[bases,m]}]];
   monomials=DeleteDuplicates[Table[Fold[Shuffle,tuple],{tuple,tuples}]];
    If[degree,SortBy[Table[{i,HallDegree[i]},{i,monomials}],#[[2]]&],SortBy[Table[{i,HallDegree[i]},{i,monomials}],#[[2]]&][[All,1]]]]
