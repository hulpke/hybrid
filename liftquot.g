# Code, accompanying the paper "Constructing Universal Covers of Finite
# Groups" by H. Dietrich and A. Hulpke, Older permutation group version
# (C) 2019 by the authors.
# This code requires GAP 4.11 or newer

# User functions:
#
# ModuleCover(G,module) constructs \hat H_{V,p} (where module is over GF(p))
# G should be a permutation group, module a (MeatAxe) module with generators
# corresponding to those of G
#
# LiftQuotient(hom,p) takes a homomorphism hom from an fp group to a
# permutation group, and a prime p and returns a homomorphism cov from the
# same finitely presented group to a suitable group such that
# - ker cov<=ker hom
# - ker hom/ker cov is the largest semisimple module quotient of ker hom
# in characteristic p.

# go through plain lists to avoid recompression issues
MyImmutableMatrix:=function(field,mat)
  return ImmutableMatrix(field,List(mat,r->List(r,x->x)));
end;

Absirrdim:=function(mo)
local p,e,m,f;
  if not MTX.IsIrreducible(mo) then Error("must be irred");fi;
  p:=Size(mo.field);
  while not MTX.IsAbsolutelyIrreducible(mo) do
    e:=1;
    repeat
      e:=e+1;
      f:=GF(p^e);
      m:=GModuleByMats(List(mo.generators,x->MyImmutableMatrix(f,x)),f);
    until not MTX.IsIrreducible(m);
    p:=p^e;
    mo:=MTX.CollectedFactors(m)[1][1];
  od;
  return [mo.dimension,mo.field];
end;

# module must fit the generators of the source of q
WreathModuleCoverMat:=function(G,module)
local gens,k,f,d,ad,adf,mult,p,dom,dim,mats,gen,m,i,ran,iso,fp,vecs,
      smats,spinner,idx,matovec;

  gens:=GeneratorsOfGroup(G);
  k:=Length(gens); # source might have more generators
  f:=module.field;

  d:=module.dimension;
  ad:=Absirrdim(module);
  adf:=ad[2];ad:=ad[1];
  mult:=ad*k; # multiplicity
  p:=Characteristic(f);

  # matrix rep
  dom:=LargestMovedPoint(G);

  # construct matrices for affine action on modules
  dim:=mult*d+1+dom;

  # find right indices if dimension is smaller -- must span abs. irred factor
  idx:=[1..d];
  if ad<d then
    m:=GModuleByMats(List(module.generators,x->MyImmutableMatrix(adf,x)),adf);
    vecs:=MTX.BasesMaximalSubmodules(m);
    vecs:=List(vecs[1],ShallowCopy);
    idx:=[];
    i:=1;
    while i<=d and Length(idx)<ad do
      if RankMat(Concatenation(vecs,One(module.generators[1]){[i]}))>Length(vecs) then
        Add(vecs,One(module.generators[1])[i]);
        Add(idx,i);
        vecs:=TriangulizedMat(vecs);
      fi;
      i:=i+1;
    od;
  fi;

  mats:=[];
  for gen in [1..k] do
    m:=NullMat(dim,dim,f);
    m{[1..dom]}{[1..dom]}:=PermutationMat(gens[gen],dom,f);
    for i in [1..mult] do
      ran:=dom+[(i-1)*d+1..i*d];
      m{ran}{ran}:=module.generators[gen];
    od;
    # now the vector part
    ran:=dom+(gen-1)*d*ad; # offset for copy in which this generator acts
    for i in [1..ad] do
      m[dim][ran+(i-1)*d+idx[i]]:=One(f);
    od;
    m[dim][dim]:=One(f); # affine bit
    Add(mats,ImmutableMatrix(f,m));
  od;

  matovec:=m->m[dim]{ran};

  # get relators in these generators
  iso:=IsomorphismFpGroupByGenerators(G,gens);
  fp:=Range(iso);
  vecs:=[];
  ran:=[dom+1..dim-1];
  for i in RelatorsOfFpGroup(fp) do
    m:=MappedWord(i,FreeGeneratorsOfFpGroup(fp),mats);
    Add(vecs,matovec(m));
  od;
  vecs:=Filtered(TriangulizedMat(vecs),x->not IsZero(x));

  #spinning setup
  smats:=List(mats,x->x{ran}{ran}); # cut out linear bit

  spinner:=function(sub)
  local vecs,i,gen,m,bas;
    vecs:=List(sub,ShallowCopy);
    bas:=TriangulizedMat(vecs);
    for i in vecs do
      for gen in smats do
        m:=i*gen;
        if SolutionMat(bas,m)=fail then
          Add(vecs,m);
          Add(bas,m);
          bas:=TriangulizedMat(bas);
        fi;
      od;
    od;
    vecs:=TriangulizedMat(vecs);
    return vecs;
  end;

  vecs:=spinner(vecs); # find full submodule for the group

  m:=Group(mats);
  SetSize(m,Size(G)*Size(f)^Length(vecs));
  return rec(group:=m,matovec:=matovec,spinner:=spinner);
end;

# module must fit the generators of the source of q
WreathModuleCoverPerm:=function(G,module)
local gens,f,d,ad,adf,mult,p,sdp,iso,i,m,conjs,ab,bas,l,prd,perms,j,k,n,clo,
 dom,dim,mats,gen,ran,fp,vecs,smats,idx;

  gens:=GeneratorsOfGroup(G);
  n:=Length(gens); # source might have more generators
  f:=module.field;

  d:=module.dimension;
  ad:=Absirrdim(module);
  adf:=ad[2];ad:=ad[1];
  p:=Characteristic(f);

  # find right indices if dimension is smaller -- must span abs. irred factor
  idx:=[1..d];
  if ad<d then
    m:=GModuleByMats(List(module.generators,x->MyImmutableMatrix(adf,x)),adf);
    vecs:=MTX.BasesMaximalSubmodules(m);
    vecs:=List(vecs[1],ShallowCopy);
    idx:=[];
    i:=1;
    while i<=d and Length(idx)<ad do
      if RankMat(Concatenation(vecs,One(module.generators[1]){[i]}))>Length(vecs) then
        Add(vecs,One(module.generators[1])[i]);
        Add(idx,i);
        vecs:=TriangulizedMat(vecs);
      fi;
      i:=i+1;
    od;
  fi;
  Print("idx=",idx,"\n");

  # make permutation version of module
  clo:=PermrepSemidirectModule(G,module);
  #if p^d<50 then
  #  # just do it
  #  ab:=AbelianGroup(ListWithIdenticalEntries(d,p));
  #  ab:=Range(RegularActionHomomorphism(ab));
  #  bas:=Pcgs(ab);
  ##else
  #  m:=Group(List(module.generators,x->TransposedMat(x)^-1));
  #    # enumerate orbits to find shortest
  #    ab:=Orbits(m,GF(p)^d);
  #    ab:=Filtered(ab,x->Length(x)>1);
  #    SortBy(ab,Length);
  ##    ab:=ab[1]; # shortest orbit
#
#    Print("orbit length ",Length(ab));
##    ab:=NullspaceMat(TransposedMat(ab{[1]}));
#    k:=One(module.generators[1]);
#    ab:=OnSubspacesByCanonicalBasis(ab,k);
#    ab:=Orbit(Group(module.generators),ab,OnSubspacesByCanonicalBasis);
##    # extens each ab to a basis
#    ab:=List(ab,x->Concatenation([First(k,j->SolutionMat(x,j)=fail)],x));
#    # now construct simultaneous action on subspaces
#    prd:=AbelianGroup(IsPermGroup,ListWithIdenticalEntries(Length(ab),p));
#    perms:=GeneratorsOfGroup(prd);
#    bas:=List(k,
#      x->LinearCombinationPcgs(perms,List(ab,y->SolutionMat(y,x)[1])));
#    ab:=Group(bas);
#  fi;
#
#  # action
#  conjs:=[];
#  for i in module.generators do
#    m:=List(i,x->LinearCombinationPcgs(bas,x));
#    m:=GroupHomomorphismByImagesNC(ab,ab,bas,m);
#    IsConjugatorIsomorphism(m);
#    Add(conjs,ConjugatorOfConjugatorIsomorphism(m));
#  od;
#
#  clo:=ClosureGroup(ab,conjs);

  bas:=clo.basis;
  conjs:=clo.ggens;
  l:=ListWithIdenticalEntries(Length(idx)*n,clo.group);
  Add(l,G);
  prd:=DirectProduct(l);

  # perm rep
  perms:=[];
  for i in [1..n] do
    p:=ImagesRepresentative(Embedding(prd,n*Length(idx)+1),gens[i]);
    for j in [1..Length(idx)] do
      for k in [1..n] do
        # action
        p:=p*ImagesRepresentative(Embedding(prd,n*(j-1)+k),conjs[i]);
        if i=k then
          p:=p*ImagesRepresentative(Embedding(prd,n*(j-1)+k),bas[idx[j]]);
        fi;
      od;
    od;
    Add(perms,p);
  od;
  prd:=Group(perms);
  return prd;

end;

# returns recorc with `cova`: T and `cover`: Full cover
WreathModuleCover:=function(G,module)
local g1,coh,gp,i,dom,field,fgens,l,d,gens,mc;
  field:=module.field;
  g1:=WreathModuleCoverPerm(G,module);
  mc:=WreathModuleCoverMat(G,module);
  SetSize(g1,Size(mc.group));
  #if Size(module.field)^(module.dimension^2)*Size(G)<10^6 then
  #  Size(g1:cheap);
  #else
  #  SetSize(g1,Size(RecognizeGroup(g1)));
  #fi;
  if not IsInt(LogInt(Size(g1)/Size(G),Size(field))/module.dimension) then Error("huh");fi;
  l:=[g1];
  coh:=TwoCohomologyGeneric(G,module);
  fgens:=GeneratorsOfGroup(coh.presentation.group);
  Print("cohomology dimension=",Length(coh.cohomology),"\n");
  if Length(coh.cohomology)>0 then
    for i in coh.cohomology do
      gp:=FpGroupCocycle(coh,i,true);
      gp:=Image(IsomorphismPermGroup(gp));
      repeat
        d:=SmallerDegreePermutationRepresentation(gp);
        if Source(d)<>Range(d) then
          gp:=Group(List(GeneratorsOfGroup(gp),x->ImagesRepresentative(d,x)));
        fi;
      until Source(d)=Range(d) or NrMovedPoints(gp)^2*4<=Size(gp);
      dom:=LargestMovedPoint(gp);
      # now find suitable generators
      gens:=List(coh.presentation.prewords,
        x->MappedWord(x,fgens,GeneratorsOfGroup(gp){[1..Length(fgens)]}));
      if Size(Group(gens))<Size(gp) then
        d:=Concatenation(GeneratorsOfGroup(coh.group),
          ListWithIdenticalEntries(
            Length(GeneratorsOfGroup(gp))-Length(GeneratorsOfGroup(coh.group)),
            One(coh.group)));
        d:=GroupHomomorphismByImages(gp,coh.group,GeneratorsOfGroup(gp),d);
        d:=KernelOfMultiplicativeGeneralMapping(d);
        while Size(Group(gens))<Size(gp) do
          for i in [1..Length(gens)] do
            gens[i]:=gens[i]*Random(d);
          od;
        od;
      fi;

      gp:=Group(gens);
      #d:=Size(gp);
      #gp:=Group(List(gens,x->PermutationMat(x,dom,field)));
      #SetSize(gp,d);
      #gp:=FaithfulConstituentMatrixGroup(gp);
      Add(l,gp);
    od;
    for i in [1..Length(l)] do
      if not IsPermGroup(l[i]) then
        d:=IsomorphismPermGroup(l[i]);
        d:=d*SmallerDegreePermutationRepresentation(Image(d):cheap);
        d:=List(GeneratorsOfGroup(l[i]),x->ImagesRepresentative(d,x));
        l[i]:=GroupWithGenerators(d);
      fi;
    od;
    d:=DirectProduct(l);
    fgens:=List([1..Length(GeneratorsOfGroup(G))],x->Product([1..Length(l)],y->
      ImagesRepresentative(Embedding(d,y),GeneratorsOfGroup(l[y])[x])));
    gp:=Group(fgens);
    #if Size(module.field)^(module.dimension^2+Length(coh.cohomology))*Size(G)<10^6 then
    #  Size(gp:cheap);
    #else
    #  SetSize(gp,Size(RecognizeGroup(gp)));
    #fi;
    if not (IsPrimePowerInt(Size(gp)/Size(G)) and
    IsInt(LogInt(Size(gp)/Size(G),Size(field))/module.dimension)) then Error("uhu");fi;
  else
    gp:=g1;
  fi;

  return rec(cova:=g1,cover:=gp,covam:=mc,
             cnta:=LogInt(Size(g1)/Size(G),Size(field))/module.dimension,
             cntb:=LogInt(Size(gp)/Size(G),Size(field))/module.dimension);
end;

ModuleCover:=function(G,module)
local moco;
  moco:=WreathModuleCover(G,module);
  return moco.cover;
end;

LiftQuotient:=function(q,p)
local G,a,b,c,irr,newq,i,cov,ker,ext,nat,moco,doit,sma;
  G:=Source(q);
  a:=Group(List(GeneratorsOfGroup(G),x->ImagesRepresentative(q,x)));
  irr:=ValueOption("irr");
  if irr=fail then
    irr:=IrreducibleModules(a,GF(p),0);
  fi;
  if irr[1]<>GeneratorsOfGroup(a) then Error("gens");fi;
  irr:=ShallowCopy(irr[2]);
  SortBy(irr,x->x.dimension);
  newq:=[];
  ext:=[];
  for i in irr do
    Print("Irreducible Module ",Position(irr,i),", dim=",i.dimension,"\n");
    moco:=WreathModuleCover(a,i);
    # first check in matrix version whether anything interesting arises
    if Size(moco.cover)=Size(moco.cova) then
      cov:=moco.covam.group;
      ker:=List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
        GeneratorsOfGroup(cov)));
      ker:=List(ker,moco.covam.matovec);
      ker:=Filtered(TriangulizedMat(ker),x->not IsZero(x));
      ker:=moco.covam.spinner(ker);;
      # only consider if larger
      doit:=Size(cov)>p^Length(ker)*Size(a);
    else
      doit:=true;
    fi;

    if doit then
      cov:=moco.cover;
      if not IsPermGroup(cov) then
        sma:=IsomorphismPermGroup(cov);
        cov:=Group(List(GeneratorsOfGroup(cov),
          x->ImagesRepresentative(sma,x)));
      fi;
      if NrMovedPoints(cov)>1000 then
        sma:=SmallerDegreePermutationRepresentation(cov:cheap);
        b:=Size(cov);
        sma:=Group(List(GeneratorsOfGroup(cov),x->ImagesRepresentative(sma,x)));
        SetSize(sma,b);
        Print("degree reduction ",
          NrMovedPoints(cov),"->",NrMovedPoints(sma),"\n");
        cov:=sma;
      fi;
      ker:=List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
        GeneratorsOfGroup(cov)));
      ker:=SubgroupNC(cov,ker);
      ker:=NormalClosure(cov,ker);
      Print("Cover of size ",Size(cov)," extends by dimension ",
        LogInt(IndexNC(cov,ker)/Size(a),p),"\n");
      Add(ext,LogInt(IndexNC(cov,ker)/Size(a),p));
      if IndexNC(cov,ker)>Size(a) then
        Add(newq,[cov,ker,LogInt(IndexNC(cov,ker)/Size(a),p)/i.dimension]);
      fi;
    else
      Print("Cover of size ",Size(cov)," does not extend\n");
      Add(ext,0);
    fi;

  od;

  b:=List(newq,x->LogInt(IndexNC(x[1],x[2])/Size(a),p));
  Print("Now intersect covers, extend by ",ext," as ",b," to ",Sum(b),"\n");
  if ValueOption("onlydims")=true then return b;fi;
  cov:=[];
  for i in newq do
    nat:=GroupHomomorphismByImagesNC(i[1],Range(q),GeneratorsOfGroup(i[1]),
      MappingGeneratorsImages(q)[2]);
    AddNaturalHomomorphismsPool(i[1],
      KernelOfMultiplicativeGeneralMapping(nat),nat);
    PullBackNaturalHomomorphismsPool(nat);
    DoCheapActionImages(i[1]);
    CloseNaturalHomomorphismsPool(i[1],i[2]);
    if not KnownNaturalHomomorphismsPool(i[1],i[2]) then
      #TryQuotientsFromFactorSubgroups(nat,i[2],
      #  Minimum(100000,Maximum(1000,10*NrMovedPoints(Range(q)))):skip:=6);
    fi;
    #b:=i[1]/i[2];
    nat:=NaturalHomomorphismByNormalSubgroupNC(i[1],i[2]);
    sma:=List(GeneratorsOfGroup(i[1]),x->ImagesRepresentative(nat,x));
    b:=Group(sma);
    Add(cov,GroupHomomorphismByImagesNC(G,b,GeneratorsOfGroup(G),sma));
  od;

  if Length(cov)=0 then
    b:=q;
  else
    b:=List(cov,Kernel);
    b:=Intersection(b);
    b:=DefiningQuotientHomomorphism(b);
  fi;
  return b;
  return b*SmallerDegreePermutationRepresentation(Image(b));
end;

MassageEpimorphismSchurCover:=function(epi)
local a,p,primes,lifts,b,l,gens;
  a:=Image(epi);
  if not IsPermGroup(a) then
    Error("only works for permgroup images, because I'm lazy");
  fi;
  primes:=Filtered(Collected(Factors(Size(a))),x->x[2]>1);
  primes:=List(primes,x->x[1]);
  primes:=Filtered(primes,x->not IsCyclic(SylowSubgroup(a,x)));

  # now do for every prime in turn
  lifts:=[];
  for p in primes do
    l:=epi;
    repeat
      b:=Image(l);
      if not IsPermGroup(b) then
        # force perm
        l:=l*IsomorphismPermGroup(b);
        b:=Image(l);
      fi;
      gens:=MappingGeneratorsImages(l)[2];
      l:=LiftQuotient(l,p:irr:=[gens,[TrivialModule(Length(gens),GF(p))]]);
      Print(p,":",Size(Image(l)),"\n");
    until Size(Image(l))=Size(b);
    if Size(Image(l))>Size(a) then Add(lifts,l);fi;
  od;
  if Length(lifts)=0 then
    SetSize(Source(epi),Size(a));
    return IdentityMapping(a);
  fi;
  b:=MappingGeneratorsImages(lifts[1])[2];
  for p in [2..Length(lifts)] do
    b:=SubdirectDiagonalPerms(b,MappingGeneratorsImages(lifts[p])[2]);
  od;
  l:=Group(b);
  return GroupHomomorphismByImages(l,a,b,MappingGeneratorsImages(epi)[2]);
end;
