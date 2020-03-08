# Code, accompanying the paper "Constructing Universal Covers of Finite
# Groups" by H. Dietrich and A. Hulpke, Hybrid group version
# (C) 2020 by the authors.
# This code requires GAP 4.11 or newer

# User functions:
#
# WreathModuleCopverHybrid(H,module) constructs
# \hat H_{V,e} (where $e$ is given through H
# G should be a permutation group, module a (MeatAxe) module with generators
# corresponding to those of H
#
# LiftQuotientHybrid(hom,p) takes a homomorphism hom from an fp group to a
# permutation group, and a prime p and returns a homomorphism cov from the
# same finitely presented group to a suitable group such that
# - ker cov<=ker hom
# - ker hom/ker cov is the largest semisimple module quotient of ker hom
# in characteristic p.
# A list of irreducible modules to consider can be fed through the
# option `irr'.

DeclareCategory( "IsHybridGroupElement",
    IsMultiplicativeElementWithInverse and IsAssociativeElement 
    and CanEasilySortElements );
DeclareCategoryCollections( "IsHybridGroupElement" );
DeclareSynonym( "IsHybridGroup", IsGroup and IsHybridGroupElementCollection );
InstallTrueMethod( IsSubsetLocallyFiniteGroup, IsHybridGroupElementCollection );
InstallTrueMethod( IsGeneratorsOfMagmaWithInverses,
  IsHybridGroupElementCollection );

DeclareRepresentation("IsHybridGroupElementDefaultRep",
  IsPositionalObjectRep and IsHybridGroupElement,[]);

TranslatedMonoidRules:=function(monhom)
local fam,t,r,i,offset;
  fam:=FamilyObj(One(Range(monhom)));
  t:=List(RelationsOfFpMonoid(Range(monhom)),r->List(r,e->
    UnderlyingElement(PreImagesRepresentative(monhom,
      ElementOfFpMonoid(fam,e)))));

  t:=List(t,x->List(x,LetterRepAssocWord));
  offset:=1+Length(GeneratorsOfGroup(Source(monhom)));
  r:=rec(tzrules:=t,
         offset:=offset,
         starters:=List([-offset+1..offset+1],x->[]),
         freegens:=FreeGeneratorsOfFpMonoid(Range(monhom)),
         monhom:=monhom,
         monrules:=RelationsOfFpMonoid(Range(monhom)));
  for i in [1..Length(t)] do
    if Length(t[i,1])>0 then
      Add(r.starters[t[i,1][1]+offset],[t[i,1],t[i,2],i]);
    fi;
  od;
  #for i in [-offset+1..offset-1] do
  #  r.starters[i+offset]:=Filtered(t,x->Length(x[1])>0 and x[1][1]=i);
  #od;
  return r;
end;

HybridGroupElement:=function(fam,top,bottom)
  return Objectify(fam!.defaultType,[top,bottom,false,false]);
end;

InstallMethod(PrintObj,"hybrid group elements",
  [IsHybridGroupElementDefaultRep],0,
function(elm)
local has;
  Print("<");
  has:=false;
  if not IsOne(elm![1]) then
    has:=true;
    Print(elm![1]);
  fi;
  if not IsOne(elm![2]) then
    if has then Print("*");fi;
    has:=true;
    Print(elm![2]);
  fi;
  if not has then Print("one");fi;
  Print(">");
end);

InstallMethod(One,"hybrid group elements",
  [IsHybridGroupElementDefaultRep],0,
  elm->One(FamilyObj(elm)));

InstallMethod(InverseOp,"hybrid group elements",
  [IsHybridGroupElementDefaultRep],0,
function(elm)
local fam,inv,prd;
  #cache inverses
  if elm![3]<>false then
    return elm![3];
  else
    fam:=FamilyObj(elm);
     if IsBound(fam!.quickermult) and fam!.quickermult<>fail
        and not ValueOption("notranslate")=true then
      inv:=fam!.backtranslate(fam!.quickermult(elm)^-1);
    else

      # the collection is guaranteed to happen in the product routine
      inv:=\*(HybridGroupElement(fam,InverseOp(elm![1]),fam!.normalone),
        One(fam):notranslate);
      # form (a,b)*(a^-1,1)=(1,c), then (a,b)^-1=(a^-1,c^-1)
      prd:=elm*inv;
      inv:=inv*HybridGroupElement(fam,fam!.factorone,InverseOp(prd![2]));
      #if not IsOne(inv*elm) then Error("invbug");fi;
    fi;

    elm![3]:=inv;
    return inv;
  fi;

end);

InstallMethod(\=,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
  return a![1]=b![1] and a![2]=b![2];
end);

InstallMethod(\<,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
  return a![1]<b![1] or (a![1]=b![1] and a![2]<b![2]);
end);

InstallMethod(\*,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
local fam,autrace,rules,r,i,p,has,x,y,tail,popo,tzrules,offset,bd,starters,
      sta,cancel;
  fam:=FamilyObj(a);

  if IsBound(fam!.quickermult) and fam!.quickermult<>fail
    and not ValueOption("notranslate")=true then
    return fam!.backtranslate(fam!.quickermult(a)*fam!.quickermult(b));
  fi;

  autrace:=function(m,f)
  local i;
    if IsAssocWord(f) then
      f:=LetterRepAssocWord(f);
    fi;
    for i in f do
      if i>0 then m:=ImagesRepresentative(fam!.auts[i],m);
      else m:=ImagesRepresentative(fam!.autsinv[-i],m);fi;
    od;
    return m;
  end;

  x:=a![1]*b![1]; # top product
  y:=autrace(a![2],b![1])*b![2]; #bottom product

  # now reduce x with rules
  #x:=UnderlyingElement(ImagesRepresentative(fam!.monhom,
  # ElementOfFpGroup(FamilyObj(One(Source(fam!.monhom))),x)));

  tzrules:=fam!.tzrules;
  starters:=tzrules.starters;
  offset:=tzrules.offset;
  tzrules:=tzrules.tzrules;
  x:=LetterRepAssocWord(x);
  repeat
    has:=false;
    # collect from the right
    p:=Length(x);
    while p>=1 and Length(x)>0 do
      sta:=starters[x[p]+offset];
      r:=1;
      while r<=Length(sta) do
  #if sta[r,1][1]<>x[p] then Error("bla");fi;
        if Length(sta[r,1])+p-1<=Length(x)
  #and sta[r,1][1]=x[p] 
          and (Length(sta[r,1])=1 or x[p+1]=sta[r,1][2])
          and ForAll([3..Length(sta[r,1])],y->x[p+y-1]=sta[r,1][y]) then

          tail:=x{[p+Length(sta[r,1])..Length(x)]};
          #x:=Subword(x,1,p-1)*rules[r,2];
          # do free cancellation, which does not involve tails
          cancel:=0;
          bd:=Length(sta[r,2]);if p-1<bd then bd:=p-1;fi;
          while cancel<bd and x[p-1-cancel]=-sta[r,2][1+cancel] do
            cancel:=cancel+1;
          od;
          if cancel>0 then
            x:=Concatenation(x{[1..p-1-cancel]},
              sta[r,2]{[cancel+1..Length(sta[r,2])]});
          else
            x:=Concatenation(x{[1..p-1]},sta[r,2]);
          fi;

          popo:=Position(fam!.presentation.monrulpos,sta[r,3]);
          if popo<>fail and not IsOne(fam!.tails[popo]) then
            #pretail:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,
            #    ElementOfFpMonoid(FamilyObj(One(Range(fam!.monhom))),tail)));
            y:=autrace(fam!.tails[popo],tail)*y;
          fi;
          #x:=x*tail;
          # do free cancellation, which does not involve tails
          cancel:=0;
          bd:=Length(tail);if Length(x)<bd then bd:=Length(x);fi;
          while cancel<bd and x[Length(x)-cancel]=-tail[1+cancel] do
            cancel:=cancel+1;
          od;
          if cancel>0 then
            x:=Concatenation(x{[1..Length(x)-cancel]},
              tail{[cancel+1..Length(tail)]});
          else
            x:=Concatenation(x,tail);
          fi;
#Print("rewr ",x,"@",p,"->",Minimum(Length(x)+1,p+Length(sta[r,2])),"\n");

          # reset position to last where something new could happen
          p:=Minimum(Length(x)+1,p+Length(sta[r,2])); # -1 will happen immediately after this
          p:=Length(x);
          r:=Length(sta);
          has:=true;
        fi;
        r:=r+1;
      od;
      p:=p-1;
    od;
  until has=false;
  x:=AssocWordByLetterRep(FamilyObj(fam!.factorone),x);
#  if not IsOne(MappedWord(a![1]*b![1]/x,GeneratorsOfGroup(fam!.presentation.group),GeneratorsOfGroup(fam!.factgrp)))
#  then
#    Error(a![1]," * ",b![1]," = ",x);
#  fi;

#  rules:=RelationsOfFpMonoid(Range(fam!.monhom));
#  repeat
#    has:=false;
#
#    for r in [1..Length(rules)] do
#      p:=PositionWord(x,rules[r,1]);
#      if p<>fail then
#        tail:=Subword(x,p+Length(rules[r,1]),Length(x));
#        x:=Subword(x,1,p-1)*rules[r,2];
#        popo:=Position(fam!.presentation.monrulpos,r);
#        if popo<>fail and not IsOne(fam!.tails[popo]) then
#          pretail:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,
#              ElementOfFpMonoid(FamilyObj(One(Range(fam!.monhom))),tail)));
#          Error("bla");
#          y:=autrace(fam!.tails[popo],pretail)*y;
#        fi;
#        x:=x*tail;
#        has:=true;
#      fi;
#    od;
#  until has=false;
  #x:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,
  #  ElementOfFpMonoid(FamilyObj(One(Range(fam!.monhom))),x)));

  x:=HybridGroupElement(fam,x,y);

  #if IsBound(fam!.quickermult) and fam!.quickermult<>fail
  #  and not ValueOption("notranslate")=true 
  #  and x<>fam!.backtranslate(fam!.quickermult(a)*fam!.quickermult(b)) then
  #  Error("MUL");
  #fi;

  return x;
end);

HybridGroupCocycle:=function(arg)
local r,z,ogens,n,gens,str,dim,i,j,f,rels,new,quot,g,p,collect,m,e,fp,old,
      it,hom,trysy,prime,mindeg,ei,mgens,mwrd,nn,newfree,mfpi,mmats,sub,
      tab,tab0,evalprod,gensmrep,invsmrep,zerob,step,
      pcgp,pcgs,auts,aut,fam,type,tails;

  r:=arg[1];
  z:=arg[2];
  ogens:=GeneratorsOfGroup(r.presentation.group);

  dim:=r.module.dimension;
  n:=Length(ogens);

  # module 
  pcgp:=AbelianGroup(ListWithIdenticalEntries(dim,r.prime));
  pcgs:=FamilyPcgs(pcgp);

  # automorphisms for generators
  auts:=[];
  for i in [1..n] do
    aut:=[];
    for j in [1..dim] do
      Add(aut,PcElementByExponents(pcgs,r.module.generators[i][j]));
    od;
    aut:=GroupHomomorphismByImages(pcgp,pcgp,pcgs,aut);
IsBijective(aut);
    SetIsBijective(aut,true);
    Add(auts,aut);
  od;

  fam:=NewFamily("Hybrid elements family",IsHybridGroupElement);
  fam!.presentation:=r.presentation;
  fam!.factgrp:=r.group;
  fam!.monhom:=r.monhom;
  fam!.tzrules:=TranslatedMonoidRules(fam!.monhom);
  fam!.fphom:=r.fphom;
  fam!.auts:=auts;
  fam!.autsinv:=List(auts,Inverse);
  fam!.factorone:=One(r.presentation.group);
  fam!.normalone:=One(pcgp);
  fam!.normal:=pcgp;
  type:=NewType(fam,IsHybridGroupElementDefaultRep);
  fam!.defaultType:=type;
  SetOne(fam,HybridGroupElement(fam,fam!.factorone,fam!.normalone));
  gens:=[];
  for i in GeneratorsOfGroup(r.presentation.group) do
    Add(gens,HybridGroupElement(fam,i,fam!.normalone));
  od;
  for i in pcgs do
    Add(gens,HybridGroupElement(fam,fam!.factorone,i));
  od;

  # tails from cocycle
  tails:=[];
  for i in [1..Length(r.presentation.relators)] do

    #  new:=MappedWord(r.presentation.relators[i],ogens,gens{[1..n]});
    #  for j in [1..dim] do
    #    new:=new*gens[n+j]^Int(z[(i-1)*dim+j]);
    #  od;
    #  Add(rels,new);
    Add(tails,PcElementByExponents(pcgs,z{(i-1)*dim+[1..dim]}));

  od;


  fam!.tails:=tails;

  gens:=Group(gens);
  #SetSize(gens,Size(r.group)*r.prime^r.module.dimension);

  return gens;

end;

# rebuild with larger pc kernel, thus moving more of collection into the
# (presumably more efficient) kernel routines for pc groups.
# This should help with calculation speed.
ShadowHybrid:=function(fam)
local g,gens,s,i,fpcgs,npcgs,relo,pf,pfgens,rws,j,ff,fpp,npp,elm,
  newrd,pos,newpc,newpcgs,nfam,type,auts,aut,first,nat,mon,
  pres,mrels,rels,mpos,remember,monrulpos,trawrd,hom,nwf,correct,
  fpcgsgens,nff;

  if IsBound(fam!.quickermult) then return fail;fi;

  ff:=GeneratorsOfGroup(fam!.presentation.group);
  # find largest normal pcgs
  g:=fam!.factgrp;
  gens:=GeneratorsOfGroup(g);
  if IsHybridGroupElementCollection(g) then
    pos:=PositionProperty(GeneratorsOfGroup(g),x->IsOne(x![1]))-1;
  else
    s:=TrivialSubgroup(g);
    pos:=Length(gens);
    while pos>=1 and gens[pos] in RadicalGroup(g) 
        and IsNormal(ClosureGroup(s,gens[pos]),s) do
      s:=ClosureGroup(s,gens[pos]);
      pos:=pos-1;
    od;
    if pos=Length(gens) or not IsNormal(g,s)
      or ValueOption("notranslate")=true then 
      fam!.quickermult:=fail;return fail;
    fi;
  fi;

  first:=List([1..pos],x->HybridGroupElement(fam,ff[x],fam!.normalone));

  # make a new pc group
  fpcgsgens:=gens{[pos+1..Length(gens)]};

  if IsHybridGroupElementCollection(g) then
    fpcgs:=List(fpcgsgens,x->x![2]);
    fpcgs:=PcgsByPcSequence(FamilyObj(fpcgs[1]),fpcgs);
  else
    fpcgs:=PcgsByPcSequence(FamilyObj(One(g)),fpcgsgens);
  fi;

  # representatives in whole group
  fpp:=List(fpcgsgens,x->HybridGroupElement(fam,
    ff[Position(gens,x)],fam!.normalone));
  npcgs:=Pcgs(fam!.normal);
  npp:=List(npcgs,x->HybridGroupElement(fam,fam!.factorone,x));
  relo:=Concatenation(RelativeOrders(fpcgs),RelativeOrders(npcgs));

  # translation of exponents > relord/2: The rewriting system represents
  # powers as a^-(p-1)/2..a^(p-1)/2, while the pcgs uses a^0..a^(p-1).
  # Note that (if e>(p-1)/2) we have that a^e=a^p*a^(e-p).
  # Thus to translate RWS->PC, we want to consider a^-p*x in place of x, to
  # translate PC->RWS we take instead of x the product a^p*x
  correct:=[];
  for i in [1..Length(fpp)] do
    elm:=fpp[i]^relo[i];
    if IsOne(elm) then
      Add(correct,false); # no change needed
    else
      Add(correct,elm^-1);
    fi;
  od;

  pf:=FreeGroup(IsSyllableWordsFamily,Length(fpcgs)+Length(npcgs));
  pfgens:=GeneratorsOfGroup(pf);

  # translate word
  newrd:=function(a)
  local e,ep,aa,b,i;
    #b:=MappedWord(a![1],ff{[pos+1..Length(ff)]},pfgens{[1..Length(fpcgs)]})
    aa:=a;
    b:=One(pf);
    e:=ExtRepOfObj(aa![1]);
    i:=1;
    while i<Length(e) do
      ep:=e[i]-pos;
      b:=b*pfgens[ep]^(e[i+1] mod relo[ep]);
      if correct[ep]<>false and e[i+1]*2>relo[ep] then
        # we must correct, changing the element as we go on

        # forget what was before
        e:=e{[(i+2)..Length(e)]};
        e:=ObjByExtRep(FamilyObj(a![1]),e);
        aa:=HybridGroupElement(fam,e,aa![2]);
        aa:=correct[ep]*aa; # undo the p-th power implicitly added before
        e:=ExtRepOfObj(aa![1]);
        i:=1; # as head is gone
      else
        i:=i+2;
      fi;

    od;

    b:=b*LinearCombinationPcgs(pfgens{[Length(fpcgs)+1..Length(pfgens)]},
             ExponentsOfPcElement(npcgs,aa![2]));
    #Print(a,"->",b,"\n");
    return b;
  end;


  rws:=SingleCollector(pf,relo);
  # store powers
  for i in [1..Length(fpcgs)] do
    elm:=fpp[i]^relo[i];
    if not IsOne(elm) then
      SetPower(rws,i,newrd(elm));
    fi;
  od;
  for i in [1..Length(npcgs)] do
    elm:=npp[i]^relo[i+Length(fpcgs)];
    if not IsOne(elm) then
      SetPower(rws,i+Length(fpcgs),newrd(elm));
    fi;
  od;
  # store commutators
  for i in [1..Length(fpcgs)] do
    for j in [i+1..Length(fpcgs)] do
      elm:=Comm(fpp[j],fpp[i]);
      if not IsOne(elm) then
        SetCommutator(rws,j,i,newrd(elm));
      fi;
    od;
    for j in [1..Length(npcgs)] do
      elm:=Comm(npp[j],fpp[i]);
      if not IsOne(elm) then
        SetCommutator(rws,j+Length(fpcgs),i,newrd(elm));
      fi;
    od;
  od;
  for i in [1..Length(npcgs)] do
    for j in [i+1..Length(npcgs)] do
      elm:=Comm(npp[j],npp[i]);
      if not IsOne(elm) then
        SetCommutator(rws,j+Length(fpcgs),i+Length(fpcgs),newrd(elm));
      fi;
    od;
  od;
  newpc:=GroupByRws(rws);

  nfam:=NewFamily("Shadowing hybrid elements family",IsHybridGroupElement);
  type:=NewType(nfam,IsHybridGroupElementDefaultRep);
  nfam!.defaultType:=type;

  nfam!.normal:=newpc;
  nfam!.normalone:=One(newpc);

  # translate word -- no need to change as it will do multiplication,
  # possibly with negative exponents, so all OK
  newpcgs:=FamilyPcgs(newpc);
  newrd:=function(a)
  local b;
    if not IsOne(a![1]) then
      b:=MappedWord(a![1],ff{[pos+1..Length(ff)]},newpcgs{[1..Length(fpcgs)]});
    else
      b:=One(newpcgs);
    fi;
    b:=b*LinearCombinationPcgs(newpcgs{[Length(fpcgs)+1..Length(pfgens)]},
             ExponentsOfPcElement(npcgs,a![2]));
    #Print(a,"->",b,"\n");
    return b;
  end;

  # automorphisms
  auts:=[];
  for i in first do
    aut:=[];
    for j in Concatenation(fpp,npp) do
      Add(aut,newrd(j^i));
    od;
    Add(auts,GroupHomomorphismByImages(newpc,newpc,newpcgs,aut));
  od;

  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  if fail in nfam!.autsinv then Error("automorphisms are not");fi;

  # now redo factor group, presentation, etc.
  if IsHybridGroupElementCollection(fam!.factgrp) then
    nat:=FamilyObj(One(fam!.factgrp));
    pres:=nat!.presentation;
    nfam!.presentation:=pres;
    mon:=Range(nat!.monhom);
    pf:=pres.group;

    nff:=Group(List(GeneratorsOfGroup(fam!.factgrp){[1..pos]},x->
      PreImagesRepresentative(nat!.fphom,
        ElementOfFpGroup(FamilyObj(One(Range(nat!.fphom))),x![1]))));
    nfam!.factgrp:=nff;

  else
    nat:=NaturalHomomorphismByNormalSubgroup(fam!.factgrp,
      SubgroupNC(fam!.factgrp,fpcgsgens));
    nff:=Group(List(GeneratorsOfGroup(fam!.factgrp){[1..pos]},
      x->ImagesRepresentative(nat,x)));

    elm:=List(ff{[1..pos]},
      x->ElementOfFpGroup(FamilyObj(One(Source(fam!.monhom))),x));
    elm:=Concatenation(List(elm,x->[x,x^-1]));
    elm:=List(elm,x->ImagesRepresentative(fam!.monhom,x));
    elm:=List(elm,x->LetterRepAssocWord(UnderlyingElement(x))[1]);
    elm:=Set(elm);
    if elm<>[1..Length(elm)] then Error("headmon");fi;
    mpos:=Maximum(elm);
    mon:=FreeMonoid(List(GeneratorsOfMonoid(Range(fam!.monhom)){[1..mpos]},String));

    trawrd:=function(wrd)
    local i,w;
      w:=[];
      for i in LetterRepAssocWord(wrd) do
        if AbsInt(i)<=mpos then
          Add(w,i);
        fi;
      od;
      return AssocWordByLetterRep(FamilyObj(One(mon)),w);
    end;

    remember:=[];
    monrulpos:=[];
    mrels:=[];
    rels:=RelationsOfFpMonoid(Range(fam!.monhom));
    for i in [1..Length(rels)] do
      elm:=List(rels[i],trawrd);
      if elm[1]<>elm[2] and not elm in mrels then
        Add(mrels,elm);
        if i in fam!.presentation.monrulpos then
          Add(remember,Position(fam!.presentation.monrulpos,i));
          Add(monrulpos,Length(mrels));
        fi;
      fi;
    od;
    mon:=FactorFreeMonoidByRelations(mon,mrels);

    pf:=FreeGroup(List([1..pos],x->Concatenation("Q",String(x)))); 

    trawrd:=function(wrd)
    local i,w;
      w:=[];
      for i in LetterRepAssocWord(wrd) do
        if AbsInt(i)<=pos then
          Add(w,i);
        fi;
      od;
      return AssocWordByLetterRep(FamilyObj(One(pf)),w);
    end;

    pres:=rec(group:=pf,
              monrulpos:=monrulpos,
              prewords:=List(fam!.presentation.prewords,trawrd),
              relators:=List(fam!.presentation.relators{remember},trawrd));
    nfam!.presentation:=pres;
    nfam!.factgrp:=nff;

  fi;
  nfam!.factorone:=One(pres.group);
  SetOne(nfam,HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone));

  gens:=[];
  for i in GeneratorsOfGroup(pres.group) do
    Add(gens,HybridGroupElement(nfam,i,nfam!.normalone));
  od;
  for i in newpcgs do
    Add(gens,HybridGroupElement(nfam,nfam!.factorone,i));
  od;

  # recalculate tails
  nfam!.tails:=List(pres.relators,x->Inverse(newrd(MappedWord(x,
    GeneratorsOfGroup(pres.group),first))));

  nwf:=FamilyObj(One(pf));
  pf:=pres.group/pres.relators;

  nfam!.monhom:=MagmaIsomorphismByFunctionsNC(pf,mon,
        function(w)
          local l,i;
          l:=[];
          for i in LetterRepAssocWord(UnderlyingElement(w)) do
            if i>0 then Add(l,2*i-1);
            else Add(l,-2*i);fi;
          od;
          return ElementOfFpMonoid(FamilyObj(One(mon)),
                  AssocWordByLetterRep(FamilyObj(UnderlyingElement(One(mon))),l));
        end,
        function(w)
          local g,i,x;
          g:=[];
          for i in LetterRepAssocWord(UnderlyingElement(w)) do
            if IsOddInt(i) then x:=(i+1)/2;
            else x:=-i/2;fi;
            # word must be freely cancelled
            if Length(g)>0 and x=-g[Length(g)] then
              Unbind(g[Length(g)]);
            else Add(g,x); fi;
          od;
          return ElementOfFpGroup(FamilyObj(One(pf)),
                  AssocWordByLetterRep(FamilyObj(UnderlyingElement(One(FreeGroupOfFpGroup(pf)))),g));
        end);
  nfam!.tzrules:=TranslatedMonoidRules(nfam!.monhom);

  nfam!.quickermult:=fail;
  nfam!.isShadowFamily:=true;

#Error("KUH");

  # translation functions

  ff:=newpcgs{[Length(newpcgs)-Length(npcgs)+1..Length(newpcgs)]};

  pfgens:=GeneratorsOfGroup(fam!.presentation.group);
  pfgens:=pfgens{[pos+1..Length(pfgens)]};

  fam!.backtranslate:=function(a)
  local h,b,i,j,c,e;
    h:=LetterRepAssocWord(a![1]);
    h:=AssocWordByLetterRep(FamilyObj(One(fam!.presentation.group)),h);
    c:=a![2];
    b:=ExponentsOfPcElement(newpcgs,c);
    for i in [1..Length(pfgens)] do
      if b[i]*2>relo[i] then
        # rewriting system is symmetric with exponents, pcgs is not.
        h:=h*pfgens[i]^(b[i]-relo[i]);
        if correct[i]<>false then
          b:=ShallowCopy(b);
          for j in [1..i] do
            b[j]:=0; # this is already processed -- clean out
          od;
          c:=PcElementByExponents(newpcgs,b);
          c:=newpcgs[i]^relo[i]*c; # undo the -p'th power recorded before
          b:=ExponentsOfPcElement(newpcgs,c);
        fi;
      else
        h:=h*pfgens[i]^b[i];
      fi;
    od;

    h:=HybridGroupElement(fam,h,
      LinearCombinationPcgs(npcgs,b{[Length(b)-Length(npcgs)+1..Length(b)]}));
    return h;
  end;

  fam!.quickermult:=function(a)
  local i,s,b,t,n,res;
#if a![4]<>false then return a![4];fi;
    res:=[];
    b:=LetterRepAssocWord(a![1]);
    s:=1;
    while s<=Length(b) do
      # find part of head that survives
      i:=s-1;
      while i<Length(b) and AbsInt(b[i+1])<=pos do
        i:=i+1;
      od;
      t:=AssocWordByLetterRep(nwf,b{[s..i]});

      i:=i+1;
      n:=nfam!.normalone;
      while i<=Length(b) and AbsInt(b[i])>pos do
        # since we multiply/divide no problem with negative powers. 
        # TODO: More efficient, avoid iterative division.
        if b[i]>0 then
          n:=n*newpcgs[b[i]-pos];
        else
          n:=n/newpcgs[-b[i]-pos];
        fi;
        i:=i+1;
      od;
      Add(res,[t,n]);
      s:=i;
    od;

    if Length(res)>0 then
      res[Length(res)][2]:=res[Length(res)][2]
        *LinearCombinationPcgs(ff,ExponentsOfPcElement(npcgs,a![2]));
      res:=List(res,x->HybridGroupElement(nfam,x[1],x[2]));
      if Length(res)=1 then
        b:=res[1];
      else
        b:=Product(res);
      fi;
    else
      b:=HybridGroupElement(nfam,nfam!.factorone,
        LinearCombinationPcgs(ff,ExponentsOfPcElement(npcgs,a![2])));
    fi;

    #Print(a," ~> ",b," ",res,"\n");
#if fam!.backtranslate(b)<>a then Error("bobo!");
    a![4]:=b;
    return b;
  end;

#  # test
#  gens:=[];
#  for i in GeneratorsOfGroup(fam!.presentation.group) do
#    Add(gens,Objectify(fam!.defaultType,[i,fam!.normalone]));
#  od;
#  for i in npcgs do
#    Add(gens,Objectify(fam!.defaultType,[fam!.factorone,i]));
#  od;
#
#  for i in gens do
#    for j in gens do
#      elm:=i*j;
#    od;
#  od;


end;

SemidirectHybrid:=function(r,ker,auts)
local ogens,n,fam,type,gens,i;

  ogens:=GeneratorsOfGroup(r.presentation.group);

  n:=Length(ogens);

  fam:=NewFamily("Hybrid elements family",IsHybridGroupElement);
  fam!.presentation:=r.presentation;
  fam!.factgrp:=r.group;
  fam!.monhom:=r.monhom;
  fam!.tzrules:=TranslatedMonoidRules(fam!.monhom);
  fam!.fphom:=r.fphom;
  fam!.auts:=auts;
  fam!.autsinv:=List(auts,Inverse);
  fam!.factorone:=One(r.presentation.group);
  fam!.normalone:=One(ker);
  fam!.normal:=ker;
  type:=NewType(fam,IsHybridGroupElementDefaultRep);
  fam!.defaultType:=type;
  SetOne(fam,HybridGroupElement(fam,fam!.factorone,fam!.normalone));
  gens:=[];
  for i in GeneratorsOfGroup(r.presentation.group) do
    Add(gens,HybridGroupElement(fam,i,fam!.normalone));
  od;
  for i in GeneratorsOfGroup(ker) do
    Add(gens,HybridGroupElement(fam,fam!.factorone,i));
  od;

  # empty tails from cocycle

  fam!.tails:=ListWithIdenticalEntries(Length(r.presentation.relators),
    One(ker));
  ShadowHybrid(fam);
  gens:=Group(gens);
  #SetSize(gens,Size(r.group)*r.prime^r.module.dimension);

  return gens;

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
      m:=GModuleByMats(List(mo.generators,x->ImmutableMatrix(f,x)),f);
    until not MTX.IsIrreducible(m);
    p:=p^e;
    mo:=MTX.CollectedFactors(m)[1][1];
  od;
  return [mo.dimension,mo.field];
end;

WreathModuleSplitCoverHybrid:=function(G,r)
local module,gens,i,j,k,f,d,ad,adf,p,idx,m,vecs,ker,pcgs,aut,auts,prd,new,a,fam,
  ng,fgens,b;

  module:=r.module;
  gens:=GeneratorsOfGroup(G);
  ng:=Length(gens);
  f:=module.field;

  d:=module.dimension;
  ad:=Absirrdim(module);
  adf:=ad[2];ad:=ad[1];
  p:=Characteristic(f);

  # find right indices if dimension is smaller -- must span abs. irred factor
  idx:=[1..d];
  if ad<d then
    m:=GModuleByMats(List(module.generators,x->ImmutableMatrix(adf,x)),adf);
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

  # form semidirect product
  ker:=AbelianGroup(ListWithIdenticalEntries(d*ad*ng,p));
  pcgs:=FamilyPcgs(ker);
  auts:=[];
  for i in module.generators do
    aut:=[];
    for j in [1..ad*ng] do
      for k in [1..d] do
        Add(aut,LinearCombinationPcgs(pcgs{(j-1)*d+[1..d]},i[k]));
      od;
    od;
    aut:=GroupHomomorphismByImages(ker,ker,pcgs,aut);
    Add(auts,aut);
  od;
  prd:=SemidirectHybrid(r,ker,auts);
  fam:=FamilyObj(One(prd));
  fgens:=FreeGeneratorsOfFpGroup(Range(r.fphom));

  # now make the generators
  new:=[];
  for i in [1..ng] do
    a:=One(ker);
    # the kernel part
    for j in [1..Length(idx)] do
      a:=a*pcgs[(i-1)*ad*d+(j-1)*d+idx[j]];
    od;
#if ForAny(fam!.tails,x->not IsOne(x)) then Error("tata");fi;
    adf:=UnderlyingElement(ImagesRepresentative(r.fphom,gens[i]));
#    a:=HybridGroupElement(fam,adf,a);
#    # multiplication by one forces collecting out wrong
#    # inverses in fp rep
#Print("a=",a,"\n");
    b:=MappedWord(adf,fgens,GeneratorsOfGroup(prd){[1..Length(fgens)]});
    b:=HybridGroupElement(fam,b![1],a);
#Print("b=",b,"\n");
#    Add(new,\*(a,One(a):notranslate));
    Add(new,b);
#Print("converted to ",new[Length(new)],"\n");
  od;

  return Group(new);

end;

DoReverseWords:=function(pres,pg)
local gens,g,ep,img;
  if not IsBound(pres.reversewords) then

    gens:=List(pres.prewords,x->MappedWord(x,GeneratorsOfGroup(pres.group),
            GeneratorsOfGroup(pg)));
    g:=Group(gens);
    ep:=EpimorphismFromFreeGroup(g);

    if Size(g)<10^6 and not IsHybridGroupElementCollection(g) then
      # get shortest word form to be faster
      pres.reversewords:=[Source(ep),List(GeneratorsOfGroup(pg),
        x->Factorization(g,x))];
    else
      pres.reversewords:=[Source(ep),List(GeneratorsOfGroup(pg),
        x->PreImagesRepresentative(ep,x))];
    fi;
  fi;
  return pres.reversewords;
end;

HybridToppers:=function(G)
local map,fam;
  fam:=FamilyObj(One(G));
  if not IsBound(G!.toppers) then
    map:=DoReverseWords(fam!.presentation,fam!.factgrp);
    G!.toppers:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),
      GeneratorsOfGroup(G)));
  fi;
  return G!.toppers;
end;

HybridBits:=function(G)
local fam,top,toppers,sel,map,ker,sub,i,j,img,factor;
  fam:=FamilyObj(One(G));
  # first get the factor
  top:=List(GeneratorsOfGroup(G),x->x![1]);
  sel:=Filtered([1..Length(top)],x->not IsOne(top[x]));
  top:=List(top{sel},x->MappedWord(x,
    GeneratorsOfGroup(fam!.presentation.group),
    GeneratorsOfGroup(fam!.factgrp)));
  factor:=Group(top,One(fam!.factgrp));
    
  # evaluate relators

  #map:=DoReverseWords(fam!.presentation,fam!.factgrp);
  #img:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),
  #  GeneratorsOfGroup(G)));
  toppers:=HybridToppers(G);

  #map:=GroupGeneralMappingByImages(factor,G,
  # top,GeneratorsOfGroup(G){sel});
  #img:=List(GeneratorsOfGroup(fam!.factgrp),x->ImagesRepresentative(map,x));
  if List(toppers,x->x![1])<>GeneratorsOfGroup(fam!.presentation.group) then
    Error("gens wrong!");
  fi;
  ker:=List(fam!.presentation.relators,x->MappedWord(x,
    GeneratorsOfGroup(fam!.presentation.group),toppers));
  ker:=Set(Filtered(ker,x->not IsOne(x)));

  # strip generators of group with toppers
  ker:=Concatenation(ker,
    List(GeneratorsOfGroup(G),
        x->x/MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),
          toppers)));

  #ker:=CoKernelGensPermHom(map);

  ker:=Concatenation(ker,Filtered(GeneratorsOfGroup(G),x->IsOne(x![1])));
  ker:=List(ker,x->x![2]); # relator images
  sub:=Group(ker,fam!.normalone);

  # now form normal closure
  for i in ker do
    for j in GeneratorsOfGroup(G) do
      img:=(HybridGroupElement(fam,fam!.factorone,i)^j)![2];
      if not img in sub then
        Add(ker,img);
        sub:=ClosureGroup(sub,img);
      fi;
    od;
  od;
  sub:=Group(InducedPcgsWrtFamilyPcgs(sub),fam!.normalone);
  return [factor,sub];
end;

OwnHybrid:=function(G)
local fam,fs,pcgs,top,map,ker,auts,nfam,gens,type,i,j,tails,new,correct,newgens;
  fam:=FamilyObj(One(G));
  fs:=HybridBits(G);
  if Size(fs[1])<Size(fam!.factgrp) then
    Error("smaller factor");
  fi;
  #top:=Filtered(GeneratorsOfGroup(G),x->not IsOne(x![1]));
  #map:=GroupGeneralMappingByImages(fam!.factgrp,G,
  #  List(top,x->MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),
  #    GeneratorsOfGroup(fam!.factgrp))),
  #  top);

  # new representatives in G for factor
  #top:=List(GeneratorsOfGroup(fam!.factgrp),x->ImagesRepresentative(map,x));
  top:=HybridToppers(G);

  # compute tails wrt to top
  tails:=List(fam!.presentation.relators,x->Inverse(MappedWord(x,
    GeneratorsOfGroup(fam!.presentation.group),
    top)![2]));

#DELETE:
# # the kernel is generated by tails, generators with trivial top and then
#   # closure, *not the ker of the Hybrid bits, as we rebase!*
#   ker:=Group(tails);
#   ker:=ClosureGroup(ker,List(Filtered(GeneratorsOfGroup(G),x->IsOne(x![1])),
#     x->x![2]));
# 
#   # normal closure
#   gens:=ShallowCopy(GeneratorsOfGroup(ker));
#   for i in gens do
#     for j in GeneratorsOfGroup(G) do
#       new:=HybridGroupElement(fam,fam!.factorone,i)^j;
#       new:=new![2];
#       if not new in ker then
#         ker:=ClosureGroup(ker,new);
#         Add(gens,new);
#       fi;
#     od;
#   od;
#   if Size(ker)<>Size(fs[2]) then Error("kernel confusion");fi;

  ker:=fs[2];
  pcgs:=Pcgs(ker);

  nfam:=NewFamily("Own Hybrid elements family",IsHybridGroupElement);
  nfam!.pckern:=pcgs;
  nfam!.presentation:=fam!.presentation;
  nfam!.factgrp:=fam!.factgrp;
  nfam!.monhom:=fam!.monhom;
  nfam!.tzrules:=TranslatedMonoidRules(nfam!.monhom);
  nfam!.fphom:=fam!.fphom;
  nfam!.factorone:=fam!.factorone;
  auts:=List(top,x->GroupHomomorphismByImages(ker,ker,pcgs,
    List(pcgs,
      y->(HybridGroupElement(fam,fam!.factorone,y)^x)![2])));

  if not ForAll(auts,IsInjective) then
    Error("wrong auts!");
  fi;

  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  nfam!.normalone:=fam!.normalone;
  nfam!.normal:=ker;
  nfam!.defaultType:=NewType(nfam,IsHybridGroupElementDefaultRep);
  SetOne(nfam,HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone));
  gens:=[];
  for i in GeneratorsOfGroup(nfam!.presentation.group) do
    Add(gens,HybridGroupElement(nfam,i,nfam!.normalone));
  od;
  for i in pcgs do
    Add(gens,HybridGroupElement(nfam,nfam!.factorone,i));
  od;

  nfam!.tails:=tails;

  new:=Group(gens);

  # now recalculate the old generators in the new group

  # how do the tails change, if we go to the new top representatives?
  correct:=List(GeneratorsOfGroup(G),x->LeftQuotient(
    MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),top),x));


  newgens:=List([1..Length(GeneratorsOfGroup(G))],x->HybridGroupElement(
    nfam,GeneratorsOfGroup(G)[x]![1],correct[x]![2]));

  if ForAny(newgens,x->not x![2] in ker) then Error("corrupt");fi;

  ShadowHybrid(nfam);

  return Group(newgens);

end;

QuotientHybrid:=function(G,N)
local fam,fs,ker,pcgs,nat,nfam,auts,gens,i,type,new;

  fam:=FamilyObj(One(G));
  fs:=HybridBits(G);

  N:=Group(List(N,x->x![2]));
  nat:=NaturalHomomorphismByNormalSubgroup(fs[2],N);
  ker:=Image(nat);
  pcgs:=Pcgs(ker);

  nfam:=NewFamily("Hybrid elements family",IsHybridGroupElement);
  nfam!.presentation:=fam!.presentation;
  nfam!.factgrp:=fam!.factgrp;
  nfam!.factorone:=fam!.factorone;
  nfam!.monhom:=fam!.monhom;
  nfam!.tzrules:=TranslatedMonoidRules(nfam!.monhom);
  nfam!.fphom:=fam!.fphom;

  # transfer tails
  nfam!.tails:=List(fam!.tails,x->ImagesRepresentative(nat,x));

  # transfer automorphisms
  auts:=List(fam!.auts,hom->GroupHomomorphismByImages(ker,ker,pcgs,
    List(pcgs,x->ImagesRepresentative(nat,ImagesRepresentative(hom,
      PreImagesRepresentative(nat,x))))));

  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  nfam!.normalone:=One(Range(nat));
  nfam!.normal:=Image(nat);
  type:=NewType(nfam,IsHybridGroupElementDefaultRep);
  nfam!.defaultType:=type;
  SetOne(nfam,HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone));
  ShadowHybrid(nfam);

  gens:=[];
  for i in GeneratorsOfGroup(G) do
    Add(gens,HybridGroupElement(nfam,i![1],ImagesRepresentative(nat,i![2])));
  od;

  new:=Group(gens);
  return new;
end;

SubdirectHybrid:=function(G,H)
local fg,fh,hg,hh,head,d,e1,e2,gen1,gen2,gens,aut,auts,tails,i,nfam,type,
 new,fhp,translate;
  fg:=FamilyObj(One(G));
  fh:=FamilyObj(One(H));
  hg:=HybridBits(G);
  hh:=HybridBits(H);
  head:=List(GeneratorsOfGroup(G),x->x![1]);
  if fg!.presentation<>fh!.presentation then
    if Length(GeneratorsOfGroup(fg!.presentation.group))<>
       Length(GeneratorsOfGroup(fh!.presentation.group)) then
         fhp:=fail;
    else 
      translate:=x->MappedWord(x,GeneratorsOfGroup(fh!.presentation.group),
        GeneratorsOfGroup(fg!.presentation.group));
      fhp:=rec(group:=fg!.presentation.group,
        monrulpos:=fh!.presentation.monrulpos,
        prewords:=List(fh!.presentation.prewords,translate),
        relators:=List(fh!.presentation.relators,translate)
        );
      if IsBound(fg!.presentation.reversewords) then
        # just for comparison
        fhp.reversewords:=fg!.presentation.reversewords;
      fi;
    fi;
  else
    fhp:=fh!.presentation;
    translate:=x->x;
  fi;

  if fg!.presentation<>fhp or fg!.factgrp<>fh!.factgrp
    or head<>List(GeneratorsOfGroup(H),x->translate(x![1]))
    or Size(hg[1])<Size(fg!.factgrp) or Size(hh[1])<Size(fh!.factgrp) then
    Error("does not fit");
  fi;
  d:=DirectProduct(hg[2],hh[2]);
  e1:=Embedding(d,1);
  e2:=Embedding(d,2);
  gen1:=Pcgs(hg[2]);
  gen2:=Pcgs(hh[2]);
  gens:=Concatenation(List(gen1,x->ImagesRepresentative(e1,x)),
                      List(gen2,x->ImagesRepresentative(e2,x)));
  auts:=[];
  for i in [1..Length(fg!.auts)] do
    aut:=Concatenation(
      List(gen1,x->ImagesRepresentative(e1,ImagesRepresentative(fg!.auts[i],x))),
      List(gen2,x->ImagesRepresentative(e2,ImagesRepresentative(fh!.auts[i],x)))
    );
    aut:=GroupHomomorphismByImages(d,d,gens,aut);
    Add(auts,aut);
  od;

  nfam:=NewFamily("Hybrid elements family",IsHybridGroupElement);
  nfam!.presentation:=fg!.presentation;
  nfam!.factgrp:=fg!.factgrp;
  nfam!.monhom:=fg!.monhom;
  nfam!.tzrules:=TranslatedMonoidRules(nfam!.monhom);
  nfam!.fphom:=fg!.fphom;
  nfam!.factorone:=fg!.factorone;
  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  nfam!.normalone:=One(d);
  nfam!.normal:=d;
  type:=NewType(nfam,IsHybridGroupElementDefaultRep);
  nfam!.defaultType:=type;
  SetOne(nfam,HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone));
  gens:=[];
  for i in GeneratorsOfGroup(nfam!.presentation.group) do
    Add(gens,HybridGroupElement(nfam,i,nfam!.normalone));
  od;
  for i in GeneratorsOfGroup(d) do
    Add(gens,HybridGroupElement(nfam,nfam!.factorone,i));
  od;

  # combine tails
  tails:=[];
  for i in [1..Length(fg!.tails)] do
    Add(tails,ImagesRepresentative(e1,fg!.tails[i])
              *ImagesRepresentative(e2,fh!.tails[i]));
  od;
  nfam!.tails:=tails;

  ShadowHybrid(nfam);

  #new:=Group(gens);

  new:=[];
  for i in [1..Length(head)] do
    Add(new,HybridGroupElement(nfam,head[i],
      ImagesRepresentative(e1,GeneratorsOfGroup(G)[i]![2])
      *ImagesRepresentative(e2,GeneratorsOfGroup(H)[i]![2]) ));
  od;

  new:=Group(new);
  i:=HybridBits(new); 
  if not ForAll(tails,x->x in i[2]) then 
    # tails could lie in d but not in kernel. If so, rebase
#Error("A1");
    new:=OwnHybrid(new);
    ShadowHybrid(FamilyObj(One(new)));
  fi;

  return new;

end;

InstallMethod(ImagesRepresentative,"hybrid",FamSourceEqFamElm,
  [IsGroupGeneralMappingByImages,
    IsMultiplicativeElementWithInverse and IsHybridGroupElementDefaultRep],0,
function(hom,elm)
local src,mgi,fam,map,toppers,topi,ker,hb,r,a,topho,topdec,pchom,pre;
  mgi:=MappingGeneratorsImages(hom);
  if not IsBound(hom!.toppi) then
    # compute good generators
    src:=Source(hom);
    if GeneratorsOfGroup(src)<>mgi[1] then
      src:=Group(mgi[1]);
    fi;
    hb:=HybridBits(src);
    fam:=FamilyObj(One(src));
    map:=DoReverseWords(fam!.presentation,fam!.factgrp);
    toppers:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),mgi[1]));
    topi:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),mgi[2]));
    ker:=[];
    for r in fam!.presentation.relators do
      a:=MappedWord(r,GeneratorsOfGroup(fam!.presentation.group),toppers);
      Add(ker,[a,a![2],
              MappedWord(r,GeneratorsOfGroup(fam!.presentation.group),topi)]);
    od;
    if Size(Group(List(ker,x->x[2])))<Size(hb[2]) then
      Error("need conjugates, not yet done");
    fi;
    a:=[[],[]];
    for r in ker do
      pre:=Position(a[1],r[2]);
      if pre=fail then
        Add(a[1],r[2]);
        Add(a[2],r[3]);
      else
        if Length(a[2][pre])>Length(r[3]) then
          a[2][pre]:=r[3];
        fi;
      fi;
    od;

    pchom:=GroupGeneralMappingByImagesNC(hb[2],Range(hom),a[1],a[2]);
    pre:=List(mgi[1],x->PreImagesRepresentative(fam!.fphom,
      ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),x![1])));
    #topho:=GroupGeneralMappingByImagesNC(Group(pre),Range(hom),pre,mgi[2]);
    topho:=EpimorphismFromFreeGroup(Group(pre));
    #topdec:=GroupGeneralMappingByImagesNC(Group(pre),src,pre,mgi[1]);
    hom!.topho:=topho;
    #hom!.topdec:=topdec;
    #hom!.toppi:=[toppers,topi];
    hom!.underlyingpchom:=pchom;
#if ForAny(ker,x->ImagesRepresentative(pchom,x[2])<>x[3]) then Error("UUU"); fi;
  else
    pchom:=hom!.underlyingpchom;
    topho:=hom!.topho;
    #topdec:=hom!.topdec;
    #toppers:=hom!.toppi[1];
    #topi:=hom!.toppi[2];
    fam:=FamilyObj(One(Source(hom)));
  fi;

  # deal with generators first
  r:=Position(mgi[1],elm);
  if r<>fail then return mgi[2][r];fi;

  # now map: First  get top bit, write in generators
  r:=PreImagesRepresentative(fam!.fphom,
    ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),elm![1]));
  r:=PreImagesRepresentative(topho,r);
  a:=LeftQuotient(MappedWord(r,GeneratorsOfGroup(Source(topho)),mgi[1]),elm);
  a:=MappedWord(r,GeneratorsOfGroup(Source(topho)),mgi[2])
      *ImagesRepresentative(pchom,a![2]);

#  hb:=EpimorphismFromFreeGroup(Source(hom));
#  ker:=MappedWord(Factorization(Source(hom),elm),GeneratorsOfGroup(Source(hb)),
#    MappingGeneratorsImages(hom)[2]);
#  if ker<>a then Error("image");fi;

  return a;
end);

InstallMethod(Size,"hybrid groups",
  [IsGroup and IsHybridGroupElementCollection],0,
function(G)
  return Product(List(HybridBits(G),Size));
end);

WreathModuleCoverHybrid:=function(G,module)
local coh,splitcover,cover,i,ext;
  coh:=TwoCohomologyGeneric(G,module);
  SetSize(coh.group,Size(G));

  splitcover:=WreathModuleSplitCoverHybrid(G,coh);
  ShadowHybrid(FamilyObj(One(splitcover)));
  cover:=OwnHybrid(splitcover);
  for i in coh.cohomology do
    ext:=HybridGroupCocycle(coh,i);
    ShadowHybrid(FamilyObj(One(ext)));

    ext:=List(coh.presentation.prewords,
      x->MappedWord(x,GeneratorsOfGroup(coh.presentation.group),
        GeneratorsOfGroup(ext){[1..Length(GeneratorsOfGroup(coh.group))]}));

    cover:=SubdirectHybrid(cover,Group(ext));
  od;
  FamilyObj(One(cover))!.fphom:=coh.fphom;
  return cover;
end;

# TMP fix
InstallMethod( IsomorphismFpGroupByChiefSeries,"pc grp",true,
               [IsPcGroup,IsString], 0,
function(g,str)
  return IsomorphismFpGroupByChiefSeriesFactor(g,str,TrivialSubgroup(g));
end);

# convert (full family) hybrid to fp
FpGroupHybrid:=function(h)
local hgens,fam,fs,iso,kfp,pres,f,rels,head,tail,i,j,pcgs,gens,domon,
  fmon,rules,mhead,mtail,kermon,img,nr,ord,w,k;

  fam:=FamilyObj(One(h));
  fs:=HybridBits(h);
  domon:=Size(Source(fam!.fphom))=Size(fs[1]);

  if domon and
   Length(fam!.auts)<>Length(GeneratorsOfGroup(Range(fam!.fphom))) then
    Error("generator discrepancy");
  fi;

  if domon then
    kermon:=ShallowCopy(ConfluentMonoidPresentationForGroup(fs[2]));
    kermon.freegens:=FreeGeneratorsOfFpMonoid(Range(kermon.monhom));
    iso:=kermon!.fphom;
  else
    iso:=IsomorphismFpGroup(fs[2]);
  fi;

  kfp:=Range(iso);
  pcgs:=List(GeneratorsOfGroup(kfp),x->PreImagesRepresentative(iso,x));
  pres:=fam!.presentation;
  f:=FreeGroup(Length(fam!.auts)
       +Length(FreeGeneratorsOfFpGroup(kfp)));
  head:=GeneratorsOfGroup(f){[1..Length(fam!.auts)]};
  tail:=GeneratorsOfGroup(f){[Length(head)+1..Length(GeneratorsOfGroup(f))]};
  rels:=[];

  if domon<>false then
    fmon:=List(GeneratorsOfGroup(f),String);
    fmon:=Concatenation(List(fmon,x->[x,Concatenation(x,"^-1")]));
    fmon:=FreeMonoid(fmon);
    mhead:=GeneratorsOfMonoid(fmon){[1..2*(Length(head))]};
    mtail:=GeneratorsOfMonoid(fmon){
      [2*(Length(head))+1..Length(GeneratorsOfMonoid(fmon))]};
    rules:=[];
  fi;

  # relators of kernel
  for i in RelatorsOfFpGroup(kfp) do
    Add(rels,MappedWord(i,FreeGeneratorsOfFpGroup(kfp),tail));
  od;

  if domon<>false then
    for i in RelationsOfFpMonoid(Range(kermon.monhom)) do
      Add(rules,List(i,x->MappedWord(x,kermon.freegens,mtail )));
    od;
  fi;

  # action on kernel
  for i in [1..Length(fam!.auts)] do
    for j in [1..Length(pcgs)] do
      img:=ImagesRepresentative(fam!.auts[i],pcgs[j]);
      Add(rels,tail[j]^head[i]/MappedWord(ImagesRepresentative(iso,img),
        GeneratorsOfGroup(kfp),tail));
      if domon<>false then
        Add(rules,[mtail[2*j-1]*mhead[2*i-1],
          mhead[2*i-1]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img))),kermon.freegens,mtail) ]);
        Add(rules,[mtail[2*j]*mhead[2*i-1],
          mhead[2*i-1]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img^-1))),kermon.freegens,mtail) ]);

        # now map with inverse
        img:=PreImagesRepresentative(fam!.auts[i],pcgs[j]);
        Add(rules,[mtail[2*j-1]*mhead[2*i],
          mhead[2*i]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img))),kermon.freegens,mtail) ]);
        Add(rules,[mtail[2*j]*mhead[2*i],
          mhead[2*i]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img^-1))),kermon.freegens,mtail) ]);
      fi;
    od;
  od;

  # tails
  for i in [1..Length(fam!.tails)] do
    Add(rels,MappedWord(pres.relators[i],GeneratorsOfGroup(pres.group),head)
      *MappedWord(ImagesRepresentative(iso,fam!.tails[i]),
        GeneratorsOfGroup(kfp),tail));
  od;

  if domon<>false then
    for i in [1..Length(fam!.tzrules.monrules)] do
      nr:=List(fam!.tzrules.monrules[i],
             x->MappedWord(x,fam!.tzrules.freegens,mhead));
      j:=Position(pres.monrulpos,i);
      if j<>fail then
        nr[2]:=nr[2]*MappedWord(UnderlyingElement(
          ImagesRepresentative(kermon.monhom,
            ImagesRepresentative(iso,fam!.tails[j]))),kermon.freegens,mtail);
      else
        # not marked, relation due to inverse. Just calculate new tail.
        img:=[];
        for j in [1,2] do
          w:=One(h);
          for k in LetterRepAssocWord(fam!.tzrules.monrules[i][j]) do
            if IsOddInt(k) then
              k:=HybridGroupElement(fam,
                AssocWordByLetterRep(FamilyObj(One(pres.group)),[(k+1)/2]),
                fam!.normalone);
            else
              k:=HybridGroupElement(fam,
                AssocWordByLetterRep(FamilyObj(One(pres.group)),[k/2]),
                fam!.normalone)^-1;
            fi;
            w:=w*k;
          od;
          Add(img,w);
        od;
        img:=LeftQuotient(img[2],img[1]);
        nr[2]:=nr[2]*MappedWord(UnderlyingElement(
          ImagesRepresentative(kermon.monhom,
            ImagesRepresentative(iso,img![2]))),kermon.freegens,mtail);

        #if Length(nr[2])>0 then
        #  # order 2, a^-1 -> a relation
#
#          # gen pos in monoid
#          img:=Position(fam!.tzrules.freegens,fam!.tzrules.monrules[i][2]);
#          # generator in free group
#          img:=pres.group.((img+1)/2);
#          # element, inverse
#          img:=HybridGroupElement(fam,img,fam!.normalone)^-1;
#          nr[2]:=nr[2]*MappedWord(UnderlyingElement(
#            ImagesRepresentative(kermon.monhom,
#              ImagesRepresentative(iso,img![2]))),kermon.freegens,mtail);
#
#        fi;
      fi;
      Add(rules,nr);
    od;
  fi;


  f:=f/rels;
  head:=GeneratorsOfGroup(f){[1..Length(fam!.auts)]};
  tail:=GeneratorsOfGroup(f){[Length(head)+1..Length(GeneratorsOfGroup(f))]};
  gens:=[];
  for i in GeneratorsOfGroup(h) do
    Add(gens,MappedWord(i![1],GeneratorsOfGroup(pres.group),head)
      *MappedWord(ImagesRepresentative(iso,i![2]),GeneratorsOfGroup(kfp),tail));
  od;
  gens:=Group(gens);

  if domon<>false then
    nr:=ReducedConfluentRewritingSystem(Range(fam!.tzrules.monhom));
    if HasLevelsOfGenerators(OrderingOfRewritingSystem(nr)) then
      head:=LevelsOfGenerators(OrderingOfRewritingSystem(nr));
    else
      head:=List(GeneratorsOfMonoid(Range(fam!.tzrules.monhom)),x->1);
    fi;
    if HasLevelsOfGenerators(kermon.ordering) then
      tail:=LevelsOfGenerators(kermon.ordering);
    else
      tail:=List(kermon.freegens,x->1);
    fi;
    #head:=Concatenation(head,Maximum(head)+LevelsOfGenerators(kermon.ordering));
    head:=Concatenation(head+Maximum(tail),tail);
    ord:=WreathProductOrdering(fmon,head);
    fmon:=FactorFreeMonoidByRelations(fmon,rules);
    nr:=KnuthBendixRewritingSystem(FamilyObj(One(fmon)),ord);
    MakeConfluent(nr);
    rules:=Rules(nr);
    fmon:=FactorFreeMonoidByRelations(FreeMonoidOfFpMonoid(fmon),rules);
    nr:=KnuthBendixRewritingSystem(FamilyObj(One(fmon)),ord);
    MakeConfluent(nr);

    # make h generators corresponding to fp
    hgens:=[];
    for i in GeneratorsOfGroup(Range(fam!.fphom)) do
      Add(hgens,HybridGroupElement(fam,UnderlyingElement(i),fam!.normalone));
    od;
    for i in GeneratorsOfGroup(Range(iso)) do
      Add(hgens,HybridGroupElement(fam,fam!.factorone,
        PreImagesRepresentative(iso,i)));
    od;

    nr:=MakeFpGroupToFpMonoidIsomorphismGensFirst(f,fmon);
    SetConfluentMonoidPresentationForGroup(gens,
      rec(fphom:=IdentityMapping(f),
          monhom:=nr,ordering:=ord));

    SetConfluentMonoidPresentationForGroup(h,
      rec(fphom:=GroupHomomorphismByImagesNC(h,f,
            Concatenation(GeneratorsOfGroup(h),hgens),
            Concatenation(GeneratorsOfGroup(gens),GeneratorsOfGroup(f))),
        monhom:=nr,ordering:=ord));
    
  fi;

  return gens;
end;

ExtendQuotientFpToFaithfulElab:=function(fp,quot,module)
local g,p,m,e,i,j,new,str,rels,z,dim,gens,hom,r,newker,cnt,
      it,trysy,prime,mindeg,fps,ei,mgens,mwrd,nn,newfree,mfpi,mmats,sub,
      tab,tab0,evalprod,gensmrep,invsmrep,zerob,step;

  fps:=Parent(fp);
  prime:=Characteristic(module.field);
  g:=Image(quot,fp);
  hom:=GroupHomomorphismByImages(g,Group(module.generators),
    GeneratorsOfGroup(g),module.generators);

  p:=Image(quot);
  trysy:=Maximum(1000,50*IndexNC(p,SylowSubgroup(p,prime)));
  # allow to enforce test coverage
  if ValueOption("forcetest")=true then trysy:=2;fi;

  mindeg:=2;
  if IsPermGroup(p) then
    # try some cheap subgroups first
    repeat
      mindeg:=Minimum(List(OrbitsMovedPoints(p),Length))/4;

      rels:=Union(List(OrbitsMovedPoints(p),
        x->List(AllBlocks(Action(p,x)),z->x{z})));
      new:=List(rels,x->Length(Orbit(p,x,OnSets)));
      SortParallel(new,rels);
      e:=true;
      while Length(rels)>0 do
        new:=Stabilizer(p,rels[1],OnSets);
        Info(InfoExtReps,2,"Attempt index ",Index(p,new));
        # ignore any stabilized sets
        rels:=Filtered(rels,
          x->not ForAll(GeneratorsOfGroup(new),y->OnSets(x,y)=x));
        if AbelianInvariants(new)<>AbelianInvariants(PreImage(quot,new)) then
          new:=LargerQuotientBySubgroupAbelianization(quot,new);
          if NrMovedPoints(Image(DefiningQuotientHomomorphism(new)))
            <prime*NrMovedPoints(p) then
            new:=Intersection(new,Kernel(quot));
            quot:=DefiningQuotientHomomorphism(new);
            p:=Image(quot);
            g:=Image(quot,fp);
            hom:=GroupHomomorphismByImages(g,Group(module.generators),
              GeneratorsOfGroup(g),module.generators);
            Info(InfoExtReps,2,"Blocks found degree ",NrMovedPoints(p),
                 " ",Size(p));
            mindeg:=Minimum(List(OrbitsMovedPoints(p),Length))/4;
            rels:=[];
            e:=Size(p)=Size(fp); # can we stop?
          fi;
        fi;
      od;
    until e;

  fi;
  newker:=KernelOfMultiplicativeGeneralMapping(quot);
  cnt:=0;
  while IndexInWholeGroup(newker)<Size(fp) do
    if Length(GeneratorsOfGroup(p))>5 then
      e:=Size(p);
      p:=Group(SmallGeneratingSet(p));
      SetSize(p,e);
    fi;
    # we allow do go immediately to normal subgroup of index up to 4.
    # This reduces search space
    it:=DescSubgroupIterator(p:skip:=LogInt(Size(fp),2));
    repeat
      m:=NextIterator(it);
      e:=fail;
      if Index(p,m)>=mindeg and (hom=false or Size(m)=1 or
        false<>MatricesStabilizerOneDim(module.field,
          List(GeneratorsOfGroup(m),
          x->TransposedMat(ImagesRepresentative(hom,x))^-1))) then
        Info(InfoExtReps,2,"Attempt index ",Index(p,m));
        if hom=false then Info(InfoExtReps,2,"hom is false");fi;

        if hom<>false and Index(p,m)>
          # up to index
          50
          # the rewriting seems to be sufficiently spiffy that we don't
          # need to worry about this more involved process.

and false # disable as not all data there yet
          then

          # Rewriting produces a bad presentation. Rather rebuild a new
          # fp group using rewriting rules, finds its abelianization,
          # and then lift that quotient
          sub:=PreImage(quot,m);
          tab0:=AugmentedCosetTableInWholeGroup(sub);

          # primary generators
          mwrd:=List(tab0!.primaryGeneratorWords,
            x->ElementOfFpGroup(FamilyObj(One(fps)),x));
          Info(InfoExtReps,4,"mwrd=",mwrd);
          mgens:=List(mwrd,x->ImagesRepresentative(quot,x));
          nn:=Length(mgens);
          if IsPermGroup(m) then
            e:=SmallerDegreePermutationRepresentation(m);
            mfpi:=IsomorphismFpGroupByGenerators(Image(e,m),
              List(mgens,x->ImagesRepresentative(e,x)):cheap);
            mfpi:=e*mfpi;
          else
            mfpi:=IsomorphismFpGroupByGenerators(m,mgens:cheap);
          fi;
          mmats:=List(mgens,x->ImagesRepresentative(hom,x));

          i:=Concatenation(module.generators,
            ListWithIdenticalEntries(module.dimension,
              IdentityMat(module.dimension,module.field)));
          e:=List(mwrd,
            x->evalprod(LetterRepAssocWord(UnderlyingElement(x)),
            gensmrep,invsmrep,i));
          ei:=List(e,function(x)
              local i;
                i:=r.myinvers(x[1],z);
                return [i[1],i[2]-x[2]];
              end);

          newfree:=FreeGroup(nn+dim);
          gens:=GeneratorsOfGroup(newfree);
          rels:=[];

          # module relations
          for i in [1..dim] do
            Add(rels,gens[nn+i]^prime);
            for j in [1..i-1] do
              Add(rels,Comm(gens[nn+i],gens[nn+j]));
            od;
            for j in [1..Length(mgens)] do
              Add(rels,gens[nn+i]^gens[j]/
                  LinearCombinationPcgs(gens{[nn+1..nn+dim]},mmats[j][i]));
            od;
          od;       

          #extended presentation

          for i in RelatorsOfFpGroup(Range(mfpi)) do
            i:=LetterRepAssocWord(i);
            str:=evalprod(i,e,ei,mmats);
            if Length(str[1])>0 then Error("inconsistent");fi;
            Add(rels,AssocWordByLetterRep(FamilyObj(One(newfree)),i)
                      /LinearCombinationPcgs(gens{[nn+1..nn+dim]},str[2]));
          od;
          newfree:=newfree/rels; # new extension
          Assert(2,
            AbelianInvariants(newfree)=AbelianInvariants(PreImage(quot,m)));
          mfpi:=GroupHomomorphismByImagesNC(newfree,m,
            GeneratorsOfGroup(newfree),Concatenation(mgens,
              ListWithIdenticalEntries(dim,One(m))));

          # first just try a bit, and see whether this gets all (e.g. if
          # module is irreducible).
          e:=LargerQuotientBySubgroupAbelianization(mfpi,m:cheap);
          if e<>fail then
            step:=0;
            while step<=1 do
              # Now write down the combined representation in wreath

              e:=DefiningQuotientHomomorphism(e);
              # define map on subgroup.
              tab:=CopiedAugmentedCosetTable(tab0);
              tab.primaryImages:=Immutable(
                List(GeneratorsOfGroup(newfree){[1..nn]},
                  x->ImagesRepresentative(e,x)));
              TrySecondaryImages(tab);

              i:=GroupHomomorphismByImagesNC(sub,Range(e),mwrd,
                List(GeneratorsOfGroup(newfree){[1..nn]},
                  x->ImagesRepresentative(e,x)):noassert);
              SetCosetTableFpHom(i,tab);
              e:=PreImage(i,TrivialSubgroup(Range(e)));
              e:=Intersection(e,
                  KernelOfMultiplicativeGeneralMapping(quot));

              # this check is very cheap, in comparison. So just be safe
              Assert(0,ForAll(RelatorsOfFpGroup(fps),
                x->IsOne(MappedWord(x,FreeGeneratorsOfFpGroup(fps),
                  GeneratorsOfGroup(e!.quot)))));

              if step=0 then
                i:=GroupHomomorphismByImagesNC(e!.quot,p,
                  GeneratorsOfGroup(e!.quot),
                  GeneratorsOfGroup(p));
                j:=PreImage(i,m);
                if AbelianInvariants(j)=AbelianInvariants(newfree) then
                  step:=2;
                  Info(InfoExtReps,2,"Small bit did good");
                else
                  Info(InfoExtReps,2,"Need expensive version");
                  e:=LargerQuotientBySubgroupAbelianization(mfpi,m:
                    cheap:=false);
                  e:=Intersection(e,
                    KernelOfMultiplicativeGeneralMapping(quot));
                fi;
              fi;
              

              step:=step+1;
            od;

          fi;

        else
          e:=LargerQuotientBySubgroupAbelianization(quot,m);
          if e<>fail then
            e:=Intersection(e,KernelOfMultiplicativeGeneralMapping(quot));
          fi;
        fi;


        if e<>fail then
          # can we do better degree -- greedy block reduction?
          nn:=e!.quot;
          if IsTransitive(nn,MovedPoints(nn)) then
            repeat
              ei:=ShallowCopy(RepresentativesMinimalBlocks(nn,
                MovedPoints(nn)));
              SortBy(ei,x->-Length(x)); # long ones first
              j:=false;
              i:=1;
              while i<=Length(ei) and j=false do
                str:=Stabilizer(nn,ei[i],OnSets);
                if Size(Core(nn,str))=1 then
                  j:=ei[i];
                fi;
                i:=i+1;
              od;
              if j<>false then
                Info(InfoExtReps,4,"deg. improved by blocks ",Size(j));
                # action on blocks
                i:=ActionHomomorphism(nn,Orbit(nn,j,OnSets),OnSets);
                j:=Size(nn);
                # make new group to not cahe anything about old.
                nn:=Group(List(GeneratorsOfGroup(nn),
                  x->ImagesRepresentative(i,x)),());
                SetSize(nn,j);
              fi;
            until j=false;

          fi;
          if not IsIdenticalObj(nn,e!.quot) then
            Info(InfoExtReps,2,"Degree improved by factor ",
              NrMovedPoints(e!.quot)/NrMovedPoints(nn));

            e:=SubgroupOfWholeGroupByQuotientSubgroup(FamilyObj(fps),nn,
              Stabilizer(nn,1));
          fi;
        elif e=fail and IndexNC(p,m)>trysy then
          trysy:=Size(fp); # never try again
          # can the Sylow subgroup get us something?
          m:=SylowSubgroup(p,prime);
          e:=PreImage(quot,m);
          Info(InfoExtReps,2,"Sylow test for index ",IndexNC(p,m));
          i:=IsomorphismFpGroup(e:cheap); # only one TzGo
          e:=EpimorphismPGroup(Range(i),prime,PClassPGroup(m)+1);
          e:=i*e; # map onto pgroup
          j:=KernelOfMultiplicativeGeneralMapping(
              InverseGeneralMapping(e)*quot);
          i:=RandomSubgroupNotIncluding(Range(e),j,20000); # 20 seconds
          Info(InfoExtReps,2,"Sylow found ",IndexNC(p,m)," * ",
            IndexNC(Range(e),i));
          if IndexNC(Range(e),i)*IndexNC(p,m)<
              # consider permdegree up to
              100000 
              # as manageable
            then
            e:=PreImage(e,i);
            #e:=KernelOfMultiplicativeGeneralMapping(
            #  DefiningQuotientHomomorphism(i));
          else
            e:=fail; # not good
          fi;
        fi;

      else Info(InfoExtReps,4,"Don't index ",Index(p,m));
      fi;

      if e<>fail then
        # store new result, but do not immediately give up on existing
        # quotient

        i :=IndexInWholeGroup(newker);
        newker:=Core(fp,Intersection(newker,e));
        if IndexInWholeGroup(newker)>i then
          Info(InfoExtReps,1,"index ",Index(p,m)," increases factor by ",
                IndexInWholeGroup(newker)/Size(p));
        fi;
        cnt:=cnt+1;
      fi;

    until e<>fail 
      and (IndexInWholeGroup(newker)=Size(fp) or prime^cnt*Size(p)>Size(fp));

    i:=p;

    quot:=DefiningQuotientHomomorphism(newker);
    newker:=KernelOfMultiplicativeGeneralMapping(quot);
    p:=Image(quot);
    Info(InfoExtReps,1,"Redo quotient to ",NrMovedPoints(p));
    mindeg:=Maximum(mindeg,Index(i,m)-1);
    hom:=false; # we don't have hom cheaply any longer as group changed.
    # this is not an issue if module is irreducible
  od;
  if IndexInWholeGroup(fp)=1 then
    new:=quot;
  else
    new:=GroupHomomorphismByImages(fp,p,GeneratorsOfGroup(fp),
      List(GeneratorsOfGroup(fp),x->ImagesRepresentative(quot,x)));
  fi;

  new:=new*SmallerDegreePermutationRepresentation(p:cheap);
  return new;

end;


LiftQuotientHybrid:=function(q,p)
local G,a,b,irr,newq,i,j,cov,ker,ext,nat,moco,doit,sma,img,kerpc,g,oldcoh,
      fp,fam,mo;
  G:=Source(q);
  a:=List(GeneratorsOfGroup(G),x->ImagesRepresentative(q,x));
  if HasImagesSource(q) and GeneratorsOfGroup(ImagesSource(q))=a then
    a:=ImagesSource(q);
  else
    a:=Group(List(GeneratorsOfGroup(G),x->ImagesRepresentative(q,x)));
  fi;

  irr:=ValueOption("irr");
  if irr=fail then 
    if IsBound(a!.irreps) then
      irr:=First(a!.irreps,x->x[1]=p);
      if irr<>fail then irr:=irr[2]; fi;
    fi;
      
    if irr=fail then
      irr:=IrreducibleModules(a,GF(p),0);
    fi;
  fi;
  if irr[1]<>GeneratorsOfGroup(a) then Error("gens");fi;
  irr:=ShallowCopy(irr[2]);
  SortBy(irr,x->x.dimension);
  b:=ValueOption("dims");
  if b<>fail then
    irr:=Filtered(irr,x->x.dimension in b);
  fi;
  newq:=[];
  ext:=[];
#oldcoh:=fail;
  for i in irr do
    Print("Irreducible Module ",Position(irr,i),", dim=",i.dimension,"\n");
    cov:=WreathModuleCoverHybrid(a,i);
    SetSize(cov,Product(HybridBits(cov),Size));
    b:=FamilyObj(One(cov));

    ker:=List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
      GeneratorsOfGroup(cov)));

    # now form normal closure
    kerpc:=Group(List(ker,x->x![2]));
    for j in ker do
      for g in GeneratorsOfGroup(cov) do
        img:=j^g;
        if not img![2] in kerpc then
          Add(ker,img);
          kerpc:=ClosureGroup(kerpc,img![2]);
        fi;
      od;
    od;
    if Size(cov)/Size(a)>Size(kerpc) then
      Add(ext,LogInt(Size(cov)/(Size(a)*Size(kerpc)),p));
      Print("Cover of size ",Size(cov)," extends by dimension ",
        ext[Length(ext)],"\n");
      Add(newq,[cov,ker,ext[Length(ext)],QuotientHybrid(cov,ker)]);
    else
      Print("Cover of size ",Size(cov)," does not extend\n");
      Add(ext,0);
    fi;

  od;

  b:=List(newq,x->x[3]);
  Print("Now intersect covers, extend by ",ext," as ",b," to ",Sum(b),"\n");

  if Length(newq)=0 then return q;fi;

  cov:=newq[1][4];
  for i in [2..Length(newq)] do
    b:=newq[i][4]; 
    cov:=SubdirectHybrid(cov,b);
  od;

  b:=HybridBits(cov);
  SetSize(cov,Product(HybridBits(cov),Size));
  fam:=FamilyObj(One(cov));
  if IsBound(fam!.quickermult) and fam!.quickermult<>fail then
    b:=Group(List(GeneratorsOfGroup(cov),fam!.quickermult));
    SetSize(b,Size(cov));
    cov:=b;
    fam:=FamilyObj(One(cov));
    if not IsBound(fam!.fphom) and IsBound(FamilyObj(One(a))!.fphom) and
      fam!.factgrp=Source(FamilyObj(One(a))!.fphom) then
      fam!.fphom:=FamilyObj(One(a))!.fphom;
    fi;
    b:=HybridBits(cov);
  fi;

  Print("Recalculate module action\n");

  # recalculate module action
  kerpc:=Pcgs(b[2]);
  mo:=[];
  for g in GeneratorsOfGroup(cov) do
    b:=[];
    for i in kerpc do
      Add(b,ExponentsOfPcElement(kerpc,(
        HybridGroupElement(fam,fam!.factorone,i)^g)![2])*Z(p)^0);
    od;
    Add(mo,b);
  od;
  if Size(cov)=Size(Image(q)) then return q;fi;
  Print("Found module action\n");

  fp:=FpGroupHybrid(cov);
  SetSize(fp,Size(cov));
  SetIndexInWholeGroup(fp,1);
  Print("Formed fp cover\n");


  b:=FamilyObj(fp)!.wholeGroup;
  #q:=GroupHomomorphismByImages(b,Image(q),GeneratorsOfGroup(b),
  #   Concatenation(GeneratorsOfGroup(FamilyObj(One(cov))!.factgrp),ListWithIdenticalEntries(Length(kerpc),One(Range(q)))));
  #if q=fail then 
  #  Error("generator mishap");
  #  q:=GroupHomomorphismByImages(fp,Image(q),
  #    GeneratorsOfGroup(fp),MappingGeneratorsImages(q)[2]);
  #fi;
  ## data for permrep
  #mo:=GModuleByMats(mo,GF(p));
  #fp!.permrepdata:=[q,mo];

  b:=GroupHomomorphismByImages(G,cov,GeneratorsOfGroup(G),GeneratorsOfGroup(cov));
  SetImagesSource(b,cov);
  if ValueOption("irr")=fail then
    cov!.irreps:=[[p,[GeneratorsOfGroup(cov),irr]]];
  fi;
  return b;

end;


