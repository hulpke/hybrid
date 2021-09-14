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

if not IsBound(IsHybridGroupElement) then
  DeclareCategory( "IsHybridGroupElement",
      IsMultiplicativeElementWithInverse and IsAssociativeElement 
      and CanEasilySortElements );
  DeclareCategoryCollections( "IsHybridGroupElement" );
  DeclareSynonym( "IsHybridGroup", IsGroup and IsHybridGroupElementCollection );
  InstallTrueMethod( IsSubsetLocallyFiniteGroup, IsHybridGroupElementCollection );
  InstallTrueMethod( IsGeneratorsOfMagmaWithInverses,
    IsHybridGroupElementCollection );
fi;

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

BindGlobal("HybridAutMats",function(fam)
local g,gf,m,mats,a,pcgs;
  #g:=Source(fam!.auts[1]);
  g:=fam!.normal;
  if Size(g)>1 and IsElementaryAbelian(g) then
    if IsPcGroup(g) then
      pcgs:=CanonicalPcgs(InducedPcgsWrtFamilyPcgs(g));
    else
      pcgs:=Pcgs(g);
    fi;
    gf:=GF(RelativeOrders(pcgs)[1]);
    mats:=[];
    for a in fam!.auts do
      m:=List(pcgs,x->ExponentsOfPcElement(pcgs,ImagesRepresentative(a,x))*One(gf));
      Add(mats,ImmutableMatrix(gf,m));
    od;
    fam!.autgf:=gf;
    fam!.autspcgs:=pcgs;
    fam!.autmats:=mats;
    fam!.autmatsinv:=List(mats,Inverse);
  else
    fam!.autmats:=fail;
  fi;
end);

BindGlobal("HybridGroupAutrace",function(fam,m,f)
  local i,mm;
    if IsAssocWord(f) then
      f:=LetterRepAssocWord(f);
    fi;
    if fam!.autmats<>fail then
      mm:=ExponentsOfPcElement(fam!.autspcgs,m)*One(fam!.autgf);
      mm:=ImmutableVector(fam!.autgf,mm);
      for i in f do
        if i>0 then mm:=mm*fam!.autmats[i];
        else mm:=mm*fam!.autmatsinv[-i];fi;
      od;
      mm:=PcElementByExponents(fam!.autspcgs,List(mm,Int));
      return mm;
#    else 
#      mm:=fail;
    fi;
    for i in f do
      if i>0 then m:=ImagesRepresentative(fam!.auts[i],m);
      else m:=ImagesRepresentative(fam!.autsinv[-i],m);fi;
    od;
#    if mm<>fail and m<>mm then Error("AUAU");fi;
    return m;
  end);

InstallMethod(\*,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
local fam,rules,r,i,p,has,x,y,tail,popo,tzrules,offset,bd,starters,
      sta,cancel,xc;
  fam:=FamilyObj(a);

  if IsBound(fam!.quickermult) and fam!.quickermult<>fail
    and not ValueOption("notranslate")=true then
    return fam!.backtranslate(fam!.quickermult(a)*fam!.quickermult(b));
  fi;

#  autrace:=function(m,f)
#  local i;
#    if IsAssocWord(f) then
#      f:=LetterRepAssocWord(f);
#    fi;
#    for i in f do
#      if i>0 then m:=ImagesRepresentative(fam!.auts[i],m);
#      else m:=ImagesRepresentative(fam!.autsinv[-i],m);fi;
#    od;
#    return m;
#  end;

  xc:=a![1]*b![1]; # top product
  y:=HybridGroupAutrace(fam,a![2],b![1])*b![2]; #bottom product

  # now reduce x with rules

  tzrules:=fam!.tzrules;
  starters:=tzrules.starters;
  offset:=tzrules.offset;
  tzrules:=tzrules.tzrules;
  x:=LetterRepAssocWord(xc);
  # collect from the left

#lc:=0;
  repeat
    has:=false;
    p:=1;
    while p<=Length(x) do
      sta:=starters[x[p]+offset];
      r:=1;
      while r<=Length(sta) do
        if Length(sta[r,1])+p-1<=Length(x)
          # shortcut test for rest
          and (Length(sta[r,1])=1 or x[p+1]=sta[r,1][2])
          and ForAll([3..Length(sta[r,1])],y->x[p+y-1]=sta[r,1][y]) then
#lc:=lc+1;

          tail:=x{[p+Length(sta[r,1])..Length(x)]};
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
            y:=HybridGroupAutrace(fam,fam!.tails[popo],tail)*y;
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
#Print("rewl ",x,",",r,"@",p,"->",Minimum(Length(x)+1,p+Length(sta[r,2])),"\n");

          p:=0; # as +1 is next
          has:=true;
          r:=Length(sta); # to exit sta loop
        fi;
        r:=r+1;
      od;
      p:=p+1;
    od;
  until has=false;
#  xl:=x;
#
#rc:=0;
#  # check from right
#  x:=LetterRepAssocWord(xc);
#  repeat
#    has:=false;
#    # collect from the right
#    p:=Length(x);
#    while p>=1 and Length(x)>0 do
#      sta:=starters[x[p]+offset];
#      r:=1;
#      while r<=Length(sta) do
#  #if sta[r,1][1]<>x[p] then Error("bla");fi;
#        if Length(sta[r,1])+p-1<=Length(x)
#  #and sta[r,1][1]=x[p] 
#          and (Length(sta[r,1])=1 or x[p+1]=sta[r,1][2])
#          and ForAll([3..Length(sta[r,1])],y->x[p+y-1]=sta[r,1][y]) then
#rc:=rc+1;
#
#          tail:=x{[p+Length(sta[r,1])..Length(x)]};
#          #x:=Subword(x,1,p-1)*rules[r,2];
#          # do free cancellation, which does not involve tails
#          cancel:=0;
#          bd:=Length(sta[r,2]);if p-1<bd then bd:=p-1;fi;
#          while cancel<bd and x[p-1-cancel]=-sta[r,2][1+cancel] do
#            cancel:=cancel+1;
#          od;
#          if cancel>0 then
#            x:=Concatenation(x{[1..p-1-cancel]},
#              sta[r,2]{[cancel+1..Length(sta[r,2])]});
#          else
#            x:=Concatenation(x{[1..p-1]},sta[r,2]);
#          fi;
#
#          popo:=Position(fam!.presentation.monrulpos,sta[r,3]);
#          if popo<>fail and not IsOne(fam!.tails[popo]) then
#            #pretail:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,
#            #    ElementOfFpMonoid(FamilyObj(One(Range(fam!.monhom))),tail)));
##            y:=HybridGroupAutrace(fam,fam!.tails[popo],tail)*y;
#          fi;
#          #x:=x*tail;
#          # do free cancellation, which does not involve tails
#          cancel:=0;
#          bd:=Length(tail);if Length(x)<bd then bd:=Length(x);fi;
#          while cancel<bd and x[Length(x)-cancel]=-tail[1+cancel] do
#            cancel:=cancel+1;
#          od;
#          if cancel>0 then
#            x:=Concatenation(x{[1..Length(x)-cancel]},
#              tail{[cancel+1..Length(tail)]});
#          else
#            x:=Concatenation(x,tail);
#          fi;
##Print("rewr ",x,",",r,"@",p,"->",Minimum(Length(x)+1,p+Length(sta[r,2])),"\n");
#
#          # reset position to last where something new could happen
#          p:=Minimum(Length(x)+1,p+Length(sta[r,2])); # -1 will happen immediately after this
#          p:=Length(x);
#          r:=Length(sta);
#          has:=true;
#        fi;
#        r:=r+1;
#      od;
#      p:=p-1;
#    od;
#  until has=false;
#
#Print("Left: ",lc,"\n");
#  if x<>xl then Error("collection error");fi;

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
#          y:=HybridGroupAutrace(fam,fam!.tails[popo],pretail)*y;
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

BindGlobal("HybridConjugate",function(x,y)
local fam,h,t,a,yinv,rawinv,tz;
  fam:=FamilyObj(x);
  if IsOne(x![2]) then
    if IsOne(y![2]) then
      # check whether there is basically a rewriting rule for this
      # conjugation. Then we can look up the result without arithmetic.

      h:=LetterRepAssocWord(y![1]);
      a:=Concatenation(LetterRepAssocWord(x![1]),h);
      tz:=fam!.tzrules.tzrules;
      t:=First([1..Length(tz)],x->tz[x][1]=a);
      if t<>fail and Length(tz[t][2])>=Length(h) 
        and tz[t][2]{[1..Length(h)]}=h then
        # There is a rule, just for this

        # the rest, after cancellation
        a:=tz[t][2]{[Length(h)+1..Length(tz[t][2])]};
        a:=AssocWordByLetterRep(FamilyObj(x![1]),a);

        t:=Position(fam!.presentation.monrulpos,t);
        if t=fail then
          t:=fam!.normalone;
        else
          t:=fam!.tails[t];
        fi;
        a:=HybridGroupElement(fam,a,t);
        #if a<>x^y then Error("conjugation");fi;
        return a;
      fi;
    fi;
    h:=x;
    t:=fail;
  else
    h:=HybridGroupElement(fam,x![1],One(x![2]));
    t:=x![2];
  fi;
  if IsOne(h![1]) then
    a:=h;
  else
    Print("four\n");
    yinv:=y^-1;
    a:=yinv*h*y;
    #rawinv:=HybridGroupElement(fam,Inverse(y![1]),fam!.normalone);
    #a:=\*(rawinv,h:notranslate)*y;
    #if not IsOne(yinv![2]) then 
    #  # Need to multiply from left with (1,yinv![2])^(y![1]^-1,1)^-1
    #  if IsAbelian(fam!.normal) then
    #    a:=HybridGroupElement(fam,fam!.factorone,
    #      HybridGroupAutrace(fam,yinv![2],y![1]))*a;
    #  else
    #    rawinv:=\*(rawinv,One(fam):notranslate);
    #    a:=(HybridGroupElement(fam,fam!.factorone,yinv![2])^Inverse(rawinv))*a;
    #    Error("test this!");
    #  fi;
    #fi;
  fi;
  if t<>fail then
    a:=a*HybridGroupElement(fam,One(x![1]),HybridGroupAutrace(fam,t,y![1]));
  fi;
  #if a<>x^y then Error("conjugation");fi;
  return a;
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
    aut:=GroupHomomorphismByImagesNC(pcgp,pcgp,pcgs,aut);
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
  fam!.wholeSize:=Size(fam!.factgrp)*Size(fam!.normal);
  HybridAutMats(fam);
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

  fam!.wholeGroup:=gens;
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

    if Length(npcgs)>0 then
      b:=b*LinearCombinationPcgs(pfgens{[Length(fpcgs)+1..Length(pfgens)]},
              ExponentsOfPcElement(npcgs,aa![2]));
    fi;
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
    if not IsOne(a![2]) then
      b:=b*LinearCombinationPcgs(newpcgs{[Length(fpcgs)+1..Length(pfgens)]},
              ExponentsOfPcElement(npcgs,a![2]));
    fi;
    #Print(a,"->",b,"\n");
    return b;
  end;

  # automorphisms
  auts:=[];
  for i in first do
    aut:=[];
    for j in Concatenation(fpp,npp) do
      Add(aut,newrd(HybridConjugate(j,i)));
    od;
    Add(auts,GroupHomomorphismByImagesNC(newpc,newpc,newpcgs,aut));
  od;

  nfam!.normal:=newpc;
  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  if fail in nfam!.autsinv then Error("automorphisms are not");fi;
  HybridAutMats(nfam);

  # now redo factor group, presentation, etc.
  if IsHybridGroupElementCollection(fam!.factgrp) then
    nat:=FamilyObj(One(fam!.factgrp));
    pres:=nat!.presentation;
    nfam!.presentation:=pres;
    mon:=Range(nat!.monhom);
    pf:=pres.group;

    nff:=Group(List(GeneratorsOfGroup(fam!.factgrp){[1..pos]},x->
      PreImagesRepresentative(nat!.fphom,
        ElementOfFpGroup(FamilyObj(One(Range(nat!.fphom))),x![1]))),
          One(Source(nat!.fphom)));
    nfam!.factgrp:=nff;

  else
    nat:=NaturalHomomorphismByNormalSubgroupNC(fam!.factgrp,
      SubgroupNC(fam!.factgrp,fpcgsgens));
    nff:=Group(List(GeneratorsOfGroup(fam!.factgrp){[1..pos]},
      x->ImagesRepresentative(nat,x)),One(Range(nat)));

    elm:=List(ff{[1..pos]},
      x->ElementOfFpGroup(FamilyObj(One(Source(fam!.monhom))),x));
    elm:=Concatenation(List(elm,x->[x,x^-1]));
    elm:=List(elm,x->ImagesRepresentative(fam!.monhom,x));
    elm:=List(elm,x->LetterRepAssocWord(UnderlyingElement(x))[1]);
    elm:=Set(elm);
    if elm<>[1..Length(elm)] then Error("headmon");fi;
    if Length(elm)=0 then mpos:=0;
    else mpos:=Maximum(elm);fi;
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
  nfam!.wholeSize:=Size(nfam!.factgrp)*Size(nfam!.normal);
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
  nfam!.tails:=List(pres.relators,x->newrd(MappedWord(

    # invert before mapping, as that is cheaper
    Inverse(x),
    GeneratorsOfGroup(pres.group),first)));

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
      if Length(ff)>0 then 
        res[Length(res)][2]:=res[Length(res)][2]
          *LinearCombinationPcgs(ff,ExponentsOfPcElement(npcgs,a![2]));
      fi;
      res:=List(res,x->HybridGroupElement(nfam,x[1],x[2]));

      if Length(res)=1 then
        b:=res[1];
      else
        b:=Product(res);
      fi;
    else
      if Length(ff)=0 then
        b:=HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone);
      else
        b:=HybridGroupElement(nfam,nfam!.factorone,
          LinearCombinationPcgs(ff,ExponentsOfPcElement(npcgs,a![2])));
      fi;
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
  fam!.wholeSize:=Size(fam!.factgrp)*Size(fam!.normal);
  HybridAutMats(fam);
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

  fam!.wholeGroup:=gens;
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
  # mark elementary abelian
  SetPcSeries(pcgs,[ker,TrivialSubgroup(ker)]);
  SetIndicesNormalSteps(pcgs,[1,Length(pcgs)+1]);
  SetIsPcgsElementaryAbelianSeries(pcgs,true);

  auts:=[];
  for i in module.generators do
    aut:=[];
    for j in [1..ad*ng] do
      for k in [1..d] do
        Add(aut,LinearCombinationPcgs(pcgs{(j-1)*d+[1..d]},i[k]));
      od;
    od;
    aut:=GroupHomomorphismByImagesNC(ker,ker,pcgs,aut);
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

    # get shortest word form to be faster
    pres.reversewords:=[Source(ep),List(GeneratorsOfGroup(pg),
      x->Factorization(g,x))];
  fi;
  return pres.reversewords;
end;

#HybridToppers:=function(G)
#local map,fam,pres,gens,gp;
#  fam:=FamilyObj(One(G));
#  if not IsBound(G!.toppers) then
#    #pres:=fam!.presentation;
#    #gens:=List(pres.prewords,x->MappedWord(x,GeneratorsOfGroup(pres.group),
#    #        GeneratorsOfGroup(fam!.factgrp))); # generators of factor we need
#    gens:=List(GeneratorsOfGroup(G),x->PreImagesRepresentative(fam!.fphom,
#        ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),x![1])));
#
#    if Size(fam!.factgrp)>10^6 or not IsPermGroup(fam!.factgrp) then
#      map:=GroupGeneralMappingByImagesNC(fam!.factgrp,G,gens,GeneratorsOfGroup(G));
#      G!.toppers:=List(GeneratorsOfGroup(fam!.factgrp),x->ImagesRepresentative(map,x));
#    else
#      gp:=Group(gens,One(fam!.factgrp));
#      map:=EpimorphismFromFreeGroup(gp);
#      G!.toppers:=List(GeneratorsOfGroup(fam!.factgrp),
#        x->MappedWord(Factorization(gp,x),
#          MappingGeneratorsImages(map)[1],GeneratorsOfGroup(G)));
#    fi;
#  fi;
#  return G!.toppers;
#end;

# this maybe should go into the library
InstallMethod( InducedPcgsByGeneratorsWithImages, "words images",true,
    [ IsPcgs and IsPrimeOrdersPcgs, IsCollection, 
      IsCollection and IsAssocWordCollection ], 0,
function( pcgs, gens, imgs )
    local  ro, max, id, igs, chain, new, seen, old, u, uw, up, e, x, c, 
           cw, d, i, j, f,nonab;

    # do family check here to avoid problems with the empty list
    if not IsIdenticalObj( FamilyObj(pcgs), FamilyObj(gens) )  then
        Error( "<pcgs> and <gens> have different families" );
    fi;
    if Length( gens ) <> Length( imgs ) then
        Error( "<gens> and <imgs> must have equal length");
    fi;

    # get the trivial case first
    if gens = AsList( pcgs ) then return [pcgs, imgs]; fi;

    #catch special case: abelian
    nonab:=not IsAbelian(Group(pcgs,OneOfPcgs(pcgs)));

    # get relative orders and composition length
    ro  := RelativeOrders(pcgs);
    max := Length(pcgs);

    # get the identity
    id := [gens[1]^0, imgs[1]^0];

    # the induced generating sequence will be collected into <igs>
    igs := List( [ 1 .. max ], x -> id );

    # <chain> gives a chain of trailing weights
    chain := max+1;

    # <new> contains a list of generators and images
    new := List( [1..Length(gens)], i -> [gens[i], imgs[i]]);
    f   := function( x, y ) 
      if DepthOfPcElement( pcgs, x[1] )=DepthOfPcElement( pcgs, y[1] )
        then return Length(x[2])>Length(y[2]);
      else
        return DepthOfPcElement( pcgs, x[1] )
                                   < DepthOfPcElement( pcgs, y[1] );
      fi;
    end;
    Sort( new, f );

    # <seen> holds a list of words already seen
    seen := Union( Set( gens ), [id[1]] );

    # start putting <new> into <igs>
    while 0 < Length(new)  do
        old := Reversed( new );
        new := [];
        for u in old do
            uw := DepthOfPcElement( pcgs, u[1] );

            # if <uw> has reached <chain>, we can ignore <u>
            if uw < chain  then
                up := [];
                repeat
                    if igs[uw][1] <> id[1]  then
                        if chain <= uw+1  then
                            u := id;
                        else
                          # is the element a shorter word?
                          if Length(igs[uw][2])>Length(u[2]) then
                            # swap
                            x:=u;
                            u:=igs[uw];
                            igs[uw]:=x;
                          fi;
                            e := LeadingExponentOfPcElement(pcgs,u[1])
                                / LeadingExponentOfPcElement(pcgs,igs[uw][1])
                                mod ro[uw];
                            u[1] := u[1] / igs[uw][1] ^ e;
                            u[2] := u[2] / igs[uw][2] ^ e;
                        fi;
                    else
                        AddSet( seen, u[1] );
                        Add( up, ShallowCopy( u ) );
                        if chain <= uw+1  then
                            u := id;
                        else
                            u[1] := u[1] ^ ro[uw];
                            u[2] := u[2] ^ ro[uw];
                        fi;
                    fi;
                    if u[1] <> id[1]  then
                        uw := DepthOfPcElement( pcgs, u[1] );
                    fi;
                until u[1] = id[1] or chain <= uw;

                # add the commutators with the powers of <u>
                for u in up do
                    for x in igs do
                        if nonab and x[1] <> id[1] 
                           and ( DepthOfPcElement(pcgs,x[1]) + 1 < chain
                              or DepthOfPcElement(pcgs,u[1]) + 1 < chain )
                        then
                            c := Comm( u[1], x[1] );
                            if not c in seen  then
                                cw := DepthOfPcElement( pcgs, c );
                                AddSet( new, [c, Comm( u[2], x[2] )] );
                                AddSet( seen, c );
                            fi;
                        fi;
                    od;
                od;

                # enter the generators <up> into <igs>
                for u in up do
                    d := DepthOfPcElement( pcgs, u[1] );
                    igs[d] := u;
                od;

                # update the chain
                while 1 < chain and igs[chain-1][1] <> id[1] do
                    chain := chain-1;
                od;

                if nonab then
                  for i  in [ chain .. max ]  do
                    for j  in [ 1 .. chain-1 ]  do
                        c := Comm( igs[i][1], igs[j][1] );
                        if not c in seen  then
                            AddSet( seen, c );
                            AddSet( new, [c, Comm( igs[i][2], igs[j][2] )] );
                        fi;
                    od;
                  od;
                fi;
#            else
#              Print("Ignore ",uw,":",Length(u[2])," ",List(igs,x->Length(x[2])),"\n");
            fi;
        od;
    od;

    # now return
    igs := Filtered( igs, x -> x <> id );
    igs := [List( igs, x -> x[1] ), List( igs, x -> x[2] )];
    igs[1] := InducedPcgsByPcSequenceNC( pcgs, igs[1] );
    return igs;
end);

# form short words in an attempt to find short relators
ShortKerWords:=function(fam,gens,free,lim)
local w,e,es,i,j,a,b,ee,p,ker,kerw;
  e:=ShallowCopy(gens);
  # inverses?
  gens:=ShallowCopy(gens);
  free:=ShallowCopy(free);
  for i in [1..Length(e)] do
    if not e[i]^-1 in gens then
      Add(gens,gens[i]^-1);
      Add(free,free[i]^-1);
    fi;
  od;
  e:=ShallowCopy(gens);
  es:=Set(e);
  ee:=List(e,x->MappedWord(x![1],
    GeneratorsOfGroup(fam!.presentation.group),
    GeneratorsOfGroup(fam!.factgrp)));
  w:=ShallowCopy(free);
  ker:=[];
  kerw:=[];
  i:=0;
  while Length(e)<lim do
    i:=i+1;
    for j in [1..Length(gens)] do
      a:=e[i]*gens[j];
      if not (a in es or IsOne(a)) then
        Add(e,a);
        AddSet(es,a);
        Add(w,w[i]*free[j]);
        b:=MappedWord(a![1],
          GeneratorsOfGroup(fam!.presentation.group),
          GeneratorsOfGroup(fam!.factgrp));
        if IsOne(b) then
          Add(ker,a);
          Add(kerw,w[Length(w)]);
        else
          p:=Position(ee,b);
          if p<>fail then
            Add(ker,a/e[p]);
            Add(kerw,w[Length(w)]/w[p]);
          else
            p:=Position(ee,b^-1);
            if p<>fail then
              Add(ker,a*e[p]);
              Add(kerw,w[Length(w)]*w[p]);
            fi;
          fi;
        fi;
        Add(ee,b);
      fi;
    od;
  od;
  # pick shortest for duplicates
  a:=Sortex(List(kerw,Length));
  ker:=Permuted(ker,a);
  kerw:=Permuted(kerw,a);
  e:=[];
  es:=[One(gens[1])];
  w:=[];
  for i in [1..Length(ker)] do
    if not ker[i] in es then
      Add(e,ker[i]);
      AddSet(es,ker[i]);
      Add(w,kerw[i]);
    fi;
  od;

  return [e,w];
end;

HybridBits:=function(G)
local fam,top,toppers,sel,map,ker,sub,i,j,img,factor,iso,fp,gf,gfg,kerw,
  xker,xkerw,addker,dowords,ffam,of;

  dowords:=ValueOption("dowords")<>false; # default to true
  if IsBound(G!.hybridbits) and (dowords=false or
    IsBound(G!.hybridbits.wordskerpcgs)) then
    return G!.hybridbits;
  fi;
  fam:=FamilyObj(One(G));
  # TODO: Re-use these free groups
  gf:=FreeGroup(Length(GeneratorsOfGroup(G))); # for word expressions
  gfg:=GeneratorsOfGroup(gf);
  #gfg:=StraightLineProgGens(gfg);

  # first get the factor
  top:=List(GeneratorsOfGroup(G),x->x![1]);
  sel:=Filtered([1..Length(top)],x->not IsOne(top[x]));
  top:=List(top{sel},x->MappedWord(x,
    GeneratorsOfGroup(fam!.presentation.group),
    GeneratorsOfGroup(fam!.factgrp)));
  factor:=Group(top,One(fam!.factgrp));

  # calculate elements corresponding to fp generators

  ker:=[];
  kerw:=[];
  xker:=[];
  xkerw:=[];
  sub:=TrivialSubgroup(fam!.normal);
  ffam:=FamilyObj(One(factor));

  # take factor and its presentation
  if Size(factor)=Size(Source(fam!.fphom)) then
    iso:=fam!.fphom;
  else
    iso:=IsomorphismFpGroup(factor);
  fi;
  fp:=Range(iso);

  if dowords then
    addker:=function(w)
    local img,i,part;
      img:=MappedWord(w,gfg,GeneratorsOfGroup(G));
      if not img![2] in sub then
        Add(ker,img);
        Add(kerw,w);
        sub:=ClosureGroup(sub,img![2]);
      elif not (IsOne(img![2]) or ForAll(kerw,i->Length(i)<Length(w))) then
        Add(xker,img);
        Add(xkerw,w);
      fi;
    end;

  else
    kerw:=ker;
    gf:=G;
    gfg:=GeneratorsOfGroup(G);
    addker:=function(w)
      if not w![2] in sub then
        Add(ker,w);
        sub:=ClosureGroup(sub,w![2]);
      fi;
    end;

  fi;

  map:=GroupGeneralMappingByImages(factor,gf,top,gfg{sel});
  if dowords=false 
      and IsHybridGroup(factor) and Size(factor)=ffam!.wholeSize then
    of:=G!.originalFactor;
    map:=GroupGeneralMappingByImages(of,gf,top,gfg{sel});
    map:=List(GeneratorsOfGroup(fp),
      x->ImagesRepresentative(map,PreImagesRepresentative(iso,x)));
  else
    map:=GroupGeneralMappingByImages(factor,gf,top,gfg{sel});
    map:=List(GeneratorsOfGroup(fp),
      x->ImagesRepresentative(map,PreImagesRepresentative(iso,x)));
  fi;

  # generators in kernel
  for i in Difference([1..Length(GeneratorsOfGroup(G))],sel) do
    addker(gfg[i]);
  od;

  # strip generators of group with representatives word and use powers.
  for i in [1..Length(sel)] do
    j:=gfg[sel[i]]/MappedWord(UnderlyingElement(
      ImagesRepresentative(iso,top[i])),
      FreeGeneratorsOfFpGroup(fp),map);
    addker(j);
    addker(gfg[sel[i]]^Order(top[i]));
  od;

  if dowords and IsPermGroup(factor) or IsPcGroup(factor) then

    # short words
    j:=ShortKerWords(fam,GeneratorsOfGroup(G){sel},gfg{sel},1000);
    for i in j[2] do
      addker(i);
    od;

    # presentation
    j:=IsomorphismFpGroupByGenerators(factor,top);
    j:=Range(j);
    for i in RelatorsOfFpGroup(j) do
      i:=MappedWord(i,FreeGeneratorsOfFpGroup(j),gfg{sel});
      addker(i);
    od;
  fi;

  if dowords and IsBound(G!.originalFactor) then
    of:=HybridBits(G!.originalFactor);
    for i in of.wordskerpcgs do
      addker(MappedWord(i,of.freegens,gfg));
    od;
  fi;

  # evaluate relators
  for i in List(RelatorsOfFpGroup(fp),
                     x->MappedWord(x,FreeGeneratorsOfFpGroup(fp),map)) do
    addker(i);
  od;

  # now form normal closure
  i:=1;
  while i<=Length(ker) do
    for j in gfg do
      addker(kerw[i]^j);
    od;
    i:=i+1;
  od;

  if dowords then
    ker:=Concatenation(ker,xker);
    kerw:=Concatenation(kerw,xkerw);
    # have short ones last (this works best with InducedPcgs...)
    j:=Sortex(-List(kerw,Length));
    ker:=Permuted(ker,j);
    kerw:=Permuted(kerw,j);

    # canonize
    i:=InducedPcgsByGeneratorsWithImages(FamilyPcgs(sub),
      List(ker,x->x![2]),kerw);
    #Error("nuno");
    
    Print(List(kerw,Length)," vs ",List(i[2],Length),"\n");
  else
    i:=[CanonicalPcgsWrtFamilyPcgs(sub)];
  fi;

  sub:=Group(i[1],fam!.normalone);
  j:=rec(factor:=factor,
          ker:=sub,
          factoriso:=iso);
  if dowords then
    j.freegens:=gfg;
    j.wordsfreps:=map;
    j.freps:=List(map,
      x->MappedWord(x,gfg,GeneratorsOfGroup(G)));
    j.kerpcgs:=i[1];
    j.wordskerpcgs:=i[2];
  else
    j.freps:=map;
  fi;
  G!.hybridbits:=j;
  return j;
end;

OwnHybrid:=function(G)
local fam,fs,pcgs,top,map,ker,auts,nfam,gens,type,i,j,tails,new,correct,newgens;
  fam:=FamilyObj(One(G));
  fs:=HybridBits(G);
  if Size(fs.factor)<Size(fam!.factgrp) then
    Error("smaller factor");
  fi;
  #top:=Filtered(GeneratorsOfGroup(G),x->not IsOne(x![1]));
  #map:=GroupGeneralMappingByImages(fam!.factgrp,G,
  #  List(top,x->MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),
  #    GeneratorsOfGroup(fam!.factgrp))),
  #  top);

  # new representatives in G for factor
  #top:=List(GeneratorsOfGroup(fam!.factgrp),x->ImagesRepresentative(map,x));
  #top:=HybridToppers(G);
  top:=fs.freps;
  if fs.factoriso<>fam!.fphom then Error("different pres");fi;

  # compute tails wrt to top
  tails:=List(fam!.presentation.relators,x->Inverse(MappedWord(x,
    GeneratorsOfGroup(fam!.presentation.group),
    top)![2]));

  ker:=fs.ker;
  # Canonical cleans out cruft
  pcgs:=CanonicalPcgs(Pcgs(ker));
  ker:=SubgroupNC(Parent(ker),pcgs);

  nfam:=NewFamily("Own Hybrid elements family",IsHybridGroupElement);
  nfam!.pckern:=pcgs;
  nfam!.presentation:=fam!.presentation;
  nfam!.factgrp:=fam!.factgrp;
  nfam!.monhom:=fam!.monhom;
  nfam!.tzrules:=TranslatedMonoidRules(nfam!.monhom);
  nfam!.fphom:=fam!.fphom;
  nfam!.factorone:=fam!.factorone;
  auts:=List(top,x->GroupHomomorphismByImagesNC(ker,ker,pcgs,
    List(pcgs,
      y->(HybridGroupElement(fam,fam!.factorone,y)^x)![2])));

  if not ForAll(auts,IsInjective) then
    Error("wrong auts!");
  fi;

  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  nfam!.normalone:=fam!.normalone;
  nfam!.normal:=ker;
  nfam!.wholeSize:=Size(nfam!.factgrp)*Size(nfam!.normal);
  HybridAutMats(nfam);
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

  new:= Group(newgens);
  nfam!.wholeGroup:=new;
  return new;

end;

QuotientHybrid:=function(G,N)
local fam,fs,ker,pcgs,nat,nfam,auts,gens,i,type,new;

  fam:=FamilyObj(One(G));
  fs:=HybridBits(G);

  N:=Group(List(N,x->x![2]),One(G)![2]);
  nat:=NaturalHomomorphismByNormalSubgroupNC(fs.ker,N);
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
  auts:=List(fam!.auts,hom->GroupHomomorphismByImagesNC(ker,ker,pcgs,
    List(pcgs,x->ImagesRepresentative(nat,ImagesRepresentative(hom,
      PreImagesRepresentative(nat,x))))));

  nfam!.auts:=auts;
  nfam!.autsinv:=List(auts,Inverse);
  nfam!.normalone:=One(Range(nat));
  nfam!.normal:=Image(nat);
  nfam!.wholeSize:=Size(nfam!.factgrp)*Size(nfam!.normal);
  HybridAutMats(nfam);
  type:=NewType(nfam,IsHybridGroupElementDefaultRep);
  nfam!.defaultType:=type;
  SetOne(nfam,HybridGroupElement(nfam,nfam!.factorone,nfam!.normalone));
  ShadowHybrid(nfam);

  gens:=[];
  for i in GeneratorsOfGroup(G) do
    Add(gens,HybridGroupElement(nfam,i![1],ImagesRepresentative(nat,i![2])));
  od;

  new:=Group(gens);
  nfam!.wholeGroup:=new;
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
    or Size(hg.factor)<Size(fg!.factgrp) or Size(hh.factor)<Size(fh!.factgrp) then
    Error("does not fit");
  fi;
  d:=DirectProduct(hg.ker,hh.ker);
  e1:=Embedding(d,1);
  e2:=Embedding(d,2);
  gen1:=Pcgs(hg.ker);
  gen2:=Pcgs(hh.ker);
  gens:=Concatenation(List(gen1,x->ImagesRepresentative(e1,x)),
                      List(gen2,x->ImagesRepresentative(e2,x)));
  auts:=[];
  for i in [1..Length(fg!.auts)] do
    aut:=Concatenation(
      List(gen1,x->ImagesRepresentative(e1,ImagesRepresentative(fg!.auts[i],x))),
      List(gen2,x->ImagesRepresentative(e2,ImagesRepresentative(fh!.auts[i],x)))
    );
    aut:=GroupHomomorphismByImagesNC(d,d,gens,aut);
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
  nfam!.wholeSize:=Size(nfam!.factgrp)*Size(nfam!.normal);
  HybridAutMats(nfam);
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
  nfam!.wholeGroup:=new;

  if IsBound(G!.originalFactor) and IsBound(H!.originalFactor) and
    G!.originalFactor=H!.originalFactor then
    new!.originalFactor:=G!.originalFactor;
  fi;
  i:=HybridBits(new); 
  if not ForAll(tails,x->x in i.ker) then 
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
local src,mgi,fam,map,toppers,topi,ker,hb,r,a,topho,topdec,pchom,pre,sub,
      pcgs,sortfun,e,ro,i,nn,ao,pres,gens;

#Error("Imgrep");
  mgi:=MappingGeneratorsImages(hom);
  src:=Source(hom);
  fam:=FamilyObj(One(src));

  # check whether it is on the standard generators of the hybrid group
  if not IsBound(hom!.onStandardGens) then
    hb:=[Filtered(mgi[1],x->IsOne(x![2]) and not IsOne(x![1])),
         Filtered(mgi[1],x->IsOne(x![1]) and not IsOne(x![2]))];
    hom!.onStandardGens:=false;
    if Length(hb[1])+Length(hb[2])=Length(mgi[1])
      and Length(Unique(hb[1]))=Length(hb[1])
      and Length(Unique(hb[2]))=Length(hb[2]) 
      and Length(mgi[1])=Length(Pcgs(fam!.normal))+Length(fam!.auts) then

      topi:=List(hb[1],x->Position(mgi[1],x));
      e:=List(hb[2],x->Position(mgi[1],x));
      a:=List(hb[2],x->x![2]);
      map:=GroupHomomorphismByImagesNC(Group(a),Range(hom),a,mgi[2]{e});
      hom!.onStandardGens:=[List(hb[1],x->x![1]),mgi[2]{topi},map];
    fi;
  fi;

  if IsList(hom!.onStandardGens) then
    a:=MappedWord(elm![1],hom!.onStandardGens[1],hom!.onStandardGens[2])*
         ImagesRepresentative(hom!.onStandardGens[3],elm![2]);
    return a;
  elif not IsBound(hom!.underlyingpchom) then
    # compute good generators
    if GeneratorsOfGroup(src)<>mgi[1] then
      src:=GroupWithGenerators(mgi[1]);
    fi;
    hb:=HybridBits(src:dowords:=true);

    pchom:=List(hb.wordskerpcgs,x->MappedWord(x,hb.freegens,mgi[2]));
    pchom:=GroupGeneralMappingByImagesNC(SubgroupNC(fam!.normal,hb.kerpcgs),
      Range(hom),hb.kerpcgs,pchom);

    topho:=[hb.factoriso,GeneratorsOfGroup(Range(hb.factoriso)),hb.freps,
            List(hb.wordsfreps,x->MappedWord(x,hb.freegens,mgi[2]))];

    hom!.topho:=topho;
    hom!.underlyingpchom:=pchom;
#  elif false then
#    nn:=List([1..Length(mgi[1])],x->Tuple([mgi[1][x],mgi[2][x]]));
#
#    gens:=List(mgi[1],x->PreImagesRepresentative(fam!.fphom,
#        ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),x![1])));
#    map:=GroupGeneralMappingByImagesNC(fam!.factgrp,Group(nn),gens,nn);
#    a:=List(GeneratorsOfGroup(fam!.factgrp),x->ImagesRepresentative(map,x));
#    toppers:=List(a,x->x[1]);
#    topi:=List(a,x->x[2]);
#
#    if not (IsPermGroup(fam!.factgrp) or IsPcGroup(fam!.factgrp)) then
#      Error("cannot factor in factor group");
#    fi;
#
#    # # need to go through words to ensure same image
#    # map:=DoReverseWords(fam!.presentation,fam!.factgrp);
#    # toppers:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),mgi[1]));
#    # topi:=List(map[2],x->MappedWord(x,GeneratorsOfGroup(map[1]),mgi[2]));
#    ker:=[];
#
#    for r in Filtered([1..Length(mgi[1])],x->IsOne(mgi[1][x]![1])) do
#      Add(ker,[mgi[1][r],mgi[1][r]![2],mgi[2][r]]);
#    od;
#
#    for r in fam!.presentation.relators do
#      a:=MappedWord(r,GeneratorsOfGroup(fam!.presentation.group),toppers);
#      if not IsOne(a) then
#        Add(ker,[a,a![2],
#                MappedWord(r,GeneratorsOfGroup(fam!.presentation.group),topi)]);
#      fi;
#    od;
#
#    sub:=Group(List(ker,x->x[2]));
#    if Size(sub)<Size(hb.ker) then
#      # clean out generators top with toppers
#      for r in [1..Length(mgi)] do
#        a:=mgi{[1,2]}[r]; # gen and image
#        e:=a[1]![1]; # top word
#        a[1]:=LeftQuotient(
#          MappedWord(e,GeneratorsOfGroup(fam!.presentation.group),
#            toppers),a[1]);
#        a[2]:=LeftQuotient(
#          MappedWord(e,GeneratorsOfGroup(fam!.presentation.group),
#            topi),a[2]);
#        if not a[1]![2] in sub then
#          Add(ker,[a[1],a[1]![2],a[2]]);
#          sub:=ClosureGroup(sub,a[1]![2]);
#        fi;
#      od;
#    fi;
#
#    pcgs:=FamilyPcgs(hb.ker);
#
#
#    if Size(hb.ker)>1 and (IsAssocWord(ker[1][3]) or IsElementOfFpGroup(ker[1][3])) then
#      e:=3*Length(pcgs);
#    else
#      e:=0;
#    fi;
#    while Size(sub)<Size(hb.ker) or e>0 do
#      repeat
#        a:=[Random(ker),Random([1..Length(mgi[1])])];
#        r:=a[1][1]^mgi[1][a[2]];
#      until not r![2] in sub or Size(sub)=Size(hb.ker);
#      Add(ker,[r,r![2],a[1][3]^mgi[2][a[2]]]);
#      sub:=ClosureGroup(sub,r![2]);
#      e:=e-1;
#    od;
#    a:=[[],[]];
#    for r in ker do
#      Add(a[1],r[2]);
#      Add(a[2],r[3]);
#    od;
#
#     ao:=List(a,ShallowCopy);
#
#    if Length(a[2])>0 and (IsAssocWord(a[2][1]) or IsElementOfFpGroup(a[2][1])) then
#      # some pre-cleaning to get shorter word lengths
#      # make pairs
#      a:=List([1..Length(a[1])],x->[a[1][x],a[2][x]]);
#      sortfun:=function(x,y)
#        return DepthOfPcElement(pcgs,x[1])<DepthOfPcElement(pcgs,y[1]) or
#          (DepthOfPcElement(pcgs,x[1])=DepthOfPcElement(pcgs,y[1]) and
#          Length(x[2])<Length(y[2]));
#        end;
#      Sort(a,sortfun);
#      while IsOne(a[Length(a)][1]) do a:=a{[1..Length(a)-1]};od;
#
#      # clean out
#      r:=1;
#      while r<Length(a) do
#        if DepthOfPcElement(pcgs,a[r][1])=DepthOfPcElement(pcgs,a[r+1][1]) then
#          ro:=RelativeOrders(pcgs)[DepthOfPcElement(pcgs,a[r][1])];
#          e:=-LeadingExponentOfPcElement(pcgs,a[r+1][1])
#            /LeadingExponentOfPcElement(pcgs,a[r][1]) mod ro;
#          if 2*e>ro then e:=e-ro;fi;
#          a[r+1]:=[a[r+1][1]*a[r][1]^e,a[r+1][2]*a[r][2]^e];
#          Sort(a,sortfun);
#          while IsOne(a[Length(a)][1]) do a:=a{[1..Length(a)-1]};od;
#        else
#          r:=r+1;
#        fi;
#      od;
#
#      # clean out (but keep old)
#      topho:=ListWithIdenticalEntries(Length(pcgs),0);
#      for r in [1..Length(a)] do
#        topho[DepthOfPcElement(pcgs,a[r][1])]:=r;
#      od;
#
#      r:=Length(a)-1;
#      while r>0 do
#        nn:=a[r];
#        pre:=ExponentsOfPcElement(pcgs,nn[1]);
#        for i in [PositionNonZero(pre)+1..Length(pre)] do
#          if topho[i]<>0 then
#            ro:=RelativeOrders(pcgs)[i];
#            e:=-pre[i]/LeadingExponentOfPcElement(pcgs,a[topho[i]][1]) mod ro;
#            if 2*e>ro then e:=e-ro;fi;
#            nn:=[nn[1]*a[topho[i]][1]^e,nn[2]*a[topho[i]][2]^e];
#            pre:=ExponentsOfPcElement(pcgs,nn[1]);
#          fi;
#        od;
#        Add(a,nn);
#
#        r:=r-1;
#      od;
#
#      # undo pairs
#      a:=[a{[1..Length(a)]}[1],a{[1..Length(a)]}[2]];
#
#    fi;
#
#    pre:=GroupGeneralMappingByImagesNC(hb.ker,Range(hom),ao[1],ao[2]);
#    pchom:=GroupGeneralMappingByImagesNC(hb.ker,Range(hom),a[1],a[2]);
#
#    if Length(a[2])>0 and (IsAssocWord(a[2][1]) or IsElementOfFpGroup(a[2][1])) then
#  Print("max",Maximum(List(pre!.sourcePcgsImages,Length))," versus ",
#        Maximum(List(pchom!.sourcePcgsImages,Length)),"\n");
#
#      if Sum(List(pre!.sourcePcgsImages,Length))
#        <Sum(List(pchom!.sourcePcgsImages,Length)) then
#        pchom:=pre;
#      fi;
#    fi;
#
#    pre:=List(mgi[1],x->PreImagesRepresentative(fam!.fphom,
#      ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),x![1])));
#
#    topho:=EpimorphismFromFreeGroup(Group(pre));
#    hom!.topho:=topho;
#    hom!.underlyingpchom:=pchom;
  else
    pchom:=hom!.underlyingpchom;
    topho:=hom!.topho;
  fi;

  # deal with generators first
  r:=Position(mgi[1],elm);
  if r<>fail then return mgi[2][r];fi;

  # now map: First  get top bit, write in generators

  r:=PreImagesRepresentative(fam!.fphom,
    ElementOfFpGroup(FamilyObj(One(Range(fam!.fphom))),elm![1]));
  r:=ImagesRepresentative(topho[1],r);
  a:=LeftQuotient(MappedWord(r,topho[2],topho[3]),elm);
  a:=MappedWord(r,topho[2],topho[4])*ImagesRepresentative(pchom,a![2]);

  #r:=PreImagesRepresentative(topho,r);
  #a:=LeftQuotient(MappedWord(r,GeneratorsOfGroup(Source(topho)),mgi[1]),elm);
  #a:=MappedWord(r,GeneratorsOfGroup(Source(topho)),mgi[2])
  #    *ImagesRepresentative(pchom,a![2]);

  return a;
end);

InstallMethod(Size,"hybrid groups",
  [IsGroup and IsHybridGroupElementCollection],0,
function(G)
local b;
  b:=HybridBits(G);
  return Size(b.factor)*Size(b.ker);
end);

WreathModuleCoverHybrid:=function(G,module)
local coh,splitcover,cover,i,ext;
  coh:=TwoCohomologyGeneric(G,module);
  SetSize(coh.group,Size(G));

  splitcover:=WreathModuleSplitCoverHybrid(G,coh);
  splitcover!.originalFactor:=G;
  ShadowHybrid(FamilyObj(One(splitcover)));
  cover:=OwnHybrid(splitcover);
  for i in coh.cohomology do
    ext:=HybridGroupCocycle(coh,i);
    ShadowHybrid(FamilyObj(One(ext)));

    ext:=List(coh.presentation.prewords,
      x->MappedWord(x,GeneratorsOfGroup(coh.presentation.group),
        GeneratorsOfGroup(ext){[1..Length(GeneratorsOfGroup(coh.group))]}));

    ext:=Group(ext);
    cover!.originalFactor:=G;
    ext!.originalFactor:=G;
    cover:=SubdirectHybrid(cover,ext);
  od;
  FamilyObj(One(cover))!.fphom:=coh.fphom;
  return cover;
end;

# TMP fix for 4.11
InstallMethod( IsomorphismFpGroupByChiefSeries,"pc grp",true,
               [IsPcGroup,IsString], 0,
function(g,str)
  return IsomorphismFpGroupByChiefSeriesFactor(g,str,TrivialSubgroup(g));
end);


if not IsBound(MakeFpGroupToMonoidHomType1) then
  Print("\n\n# Adding Compatibility routines for GAP 4.11\n",
        "# Code will not run at optimal speed\n\n");
  BindGlobal("MakeFpGroupToMonoidHomType1",function(fp,m)
  local hom;
    hom:=MagmaIsomorphismByFunctionsNC(fp,m,
          function(w)
            local l,i;
            l:=[];
            for i in LetterRepAssocWord(UnderlyingElement(w)) do
              if i>0 then Add(l,2*i-1);
              else Add(l,-2*i);fi;
            od;
            return ElementOfFpMonoid(FamilyObj(One(m)),
                    AssocWordByLetterRep(FamilyObj(One(FreeMonoidOfFpMonoid(m))),l));
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
            return ElementOfFpGroup(FamilyObj(One(fp)),
                    AssocWordByLetterRep(FamilyObj(One(FreeGroupOfFpGroup(fp))),g));
          end);

    hom!.type:=1;
    if not HasIsomorphismFpMonoid(fp) then
      SetIsomorphismFpMonoid(fp,hom);
    fi;
    return hom;
  end);

  # non-solvable cohomology based on rewriting

  # return isomorphism G-fp and fp->mon, such that presentation of monoid is
  # confluent (wrt wreath order). Returns list [fphom,monhom,ordering]
  InstallMethod(ConfluentMonoidPresentationForGroup,"generic",
    [IsGroup and IsFinite],
  function(G)
  local iso,fp,n,dec,homs,mos,i,j,ffp,imo,m,k,gens,fm,mgens,rules,
        loff,off,monreps,left,right,fmgens,r,diff,monreal,nums,reduce,hom,dept;
Error("use?");
    if IsSymmetricGroup(G) then
      i:=SymmetricGroup(SymmetricDegree(G));
      iso:=CheapIsomSymAlt(G,i)*IsomorphismFpGroup(i);
      fp:=Range(iso);
      hom:=IsomorphismFpMonoid(fp);
      m:=Range(hom);
      fm:=FreeMonoidOfFpMonoid(m);
      k:=KnuthBendixRewritingSystem(m);
      MakeConfluent(k);
      rules:=Rules(k);
      dept:=fail;
    else
      iso:=IsomorphismFpGroupByChiefSeries(G:rewrite);

      fp:=Range(iso);
      gens:=GeneratorsOfGroup(fp);
      n:=Length(gens);
      dec:=iso!.decompinfo;

      fmgens:=[];
      mgens:=[];
      for i in gens do
        Add(fmgens,i);
        Add(fmgens,i^-1);
        Add(mgens,String(i));
        Add(mgens,String(i^-1));
      od;
      nums:=List(fmgens,x->LetterRepAssocWord(UnderlyingElement(x))[1]);
      fm:=FreeMonoid(mgens);
      mgens:=GeneratorsOfMonoid(fm);
      rules:=[];
      reduce:=function(w)
      local red,i,p;
        w:=LetterRepAssocWord(w);
        repeat
          i:=1;
          red:=false;
          while i<=Length(rules) and red=false do
            p:=PositionSublist(w,LetterRepAssocWord(rules[i][1]));
            if p<>fail then
              #Print("Apply ",rules[i],p,w,"\n");
              w:=Concatenation(w{[1..p-1]},LetterRepAssocWord(rules[i][2]),
                w{[p+Length(rules[i][1])..Length(w)]});
              red:=true;
            else
              i:=i+1;
            fi;
          od;
        until red=false;
        return AssocWordByLetterRep(FamilyObj(One(fm)),w);
      end;


      homs:=ShallowCopy(dec.homs);
      mos:=[];
      off:=Length(mgens);
      dept:=[];
      # go up so we may reduce tails
      for i in [Length(homs),Length(homs)-1..1] do
        Add(dept,off);
        if IsGeneralPcgs(homs[i]) then
          ffp:=AbelianGroup(IsFpGroup,RelativeOrders(homs[i]));
        else
          ffp:=Range(dec.homs[i]);
        fi;
        imo:=IsomorphismFpMonoid(ffp);
        Add(mos,imo);
        m:=Range(imo);
        loff:=off-Length(GeneratorsOfMonoid(m));
        monreps:=fmgens{[loff+1..off]};
        monreal:=mgens{[loff+1..off]};
        if IsBound(m!.rewritingSystem) then
          k:=m!.rewritingSystem;
        else
          k:=KnuthBendixRewritingSystem(m);
        fi;
        MakeConfluent(k);
        # convert rules
        for r in Rules(k) do
          left:=MappedWord(r[1],FreeGeneratorsOfFpMonoid(m),monreps);
          right:=MappedWord(r[2],FreeGeneratorsOfFpMonoid(m),monreps);
          diff:=LeftQuotient(PreImagesRepresentative(iso,right),
                  PreImagesRepresentative(iso,left));
          diff:=ImagesRepresentative(iso,diff);

          left:=MappedWord(r[1],FreeGeneratorsOfFpMonoid(m),monreal);
          right:=MappedWord(r[2],FreeGeneratorsOfFpMonoid(m),monreal);
          if not IsOne(diff) then 
            right:=right*Product(List(LetterRepAssocWord(UnderlyingElement(diff)),
              x->mgens[Position(nums,x)]));
          fi;
          right:=reduce(right); # monoid word might change
          Add(rules,[left,right]);
        od;
        for j in [loff+1..off] do
          # if the generator gets reduced away, won't need to use it
          if reduce(mgens[j])=mgens[j] then
            for k in [off+1..Length(mgens)] do
              if reduce(mgens[k])=mgens[k] then
                right:=fmgens[j]^-1*fmgens[k]*fmgens[j];
                #collect
                right:=ImagesRepresentative(iso,PreImagesRepresentative(iso,right));
                right:=Product(List(LetterRepAssocWord(UnderlyingElement(right)),
                  x->mgens[Position(nums,x)]));
                right:=reduce(mgens[j]*right);
                Add(rules,[mgens[k]*mgens[j],right]);
              fi;
            od;
          fi;
        od;
        #if i<Length(homs) then Error("ZU");fi;
        off:=loff;
      od;
      Add(dept,off);
      # calculate levels for ordering
      dept:=dept+1;
      dept:=List([1..Length(mgens)],
        x->PositionProperty(dept,y->x>=y)-1);

      if AssertionLevel()>1 and ForAny(rules,x->x[2]<>reduce(x[2])) then Error("irreduced right");fi;

      # inverses are true inverses, also for extension
      for i in [1..Length(gens)] do
        left:=mgens[2*i-1]*mgens[2*i];
        left:=reduce(left);
        if left<>One(fm) then Add(rules,[left,One(fm)]); fi;
        left:=mgens[2*i]*mgens[2*i-1];
        left:=reduce(left);
        if left<>One(fm) then Add(rules,[left,One(fm)]); fi;
      od;
    fi;

    # finally create 
    m:=FactorFreeMonoidByRelations(fm,rules);

    hom:=MakeFpGroupToMonoidHomType1(fp,m);

    j:=rec(fphom:=iso,monhom:=hom);
    if dept=fail then
      j.ordering:=k!.ordering;
    else
      j.ordering:=WreathProductOrdering(fm,dept);
    fi;
    k:=KnuthBendixRewritingSystem(FamilyObj(One(m)),j.ordering);
    k!.reduced:=true;
    MakeConfluent(k); # will store in monoid as reducedConfluent
    return j;
  end);
fi;

#####

# convert (full family) hybrid to fp
FpGroupHybrid:=function(h)
local hgens,fam,fs,iso,kfp,pres,f,rels,head,tail,i,j,pcgs,gens,domon,
  fmon,rules,mhead,mtail,kermon,img,nr,ord,w,k,tzrules,addrule,redwith,
  fphom,kb,invliv;

#  redwith:=function(w,rule)
#  local p;
#    p:=PositionSublist(w,rule[1]);
#    while p<>fail do
#      w:=Concatenation(w{[1..p-1]},rule[2],w{[p+Length(rule[1])..Length(w)]});
#      p:=PositionSublist(w,rule[1]);
#    od;
#    return w;
#  end;

  addrule:=function(rul)
  local t;
    t:=List(rul,LetterRepAssocWord);
    #Print("Add:",rul,"\n");
    AddRuleReduced(kb,t);
#    if not t in kb!.tzrules then Error("discarded",rul,"\n"); fi;

#  local t,ot,i,w,ch,lr,lrw,sel,stack;
#    # reduce rule with existing
#
#    ot:=ShallowCopy(t);
#    t:=[ReduceLetterRepWordsRewSys(tzrules,t[1]),ReduceLetterRepWordsRewSys(tzrules,t[2])];
#
#    if t[1]=t[2] then return; fi; # rule gone
#    #if ch>0 then 
#    if t<>ot then
#      rul:=List(t,x->AssocWordByLetterRep(FamilyObj(rul[1]),x));
#      if t[1]<>ot[1] and IsLessThanOrEqualUnder(ord,rul[1],rul[2]) then
#        t:=Reversed(t);
#        rul:=Reversed(rul);
#      fi;
#    fi;
#
#    # now reduce existing rules with new
#    sel:=[1..Length(rules)];
#    stack:=[];
#    for i in [1..Length(rules)] do
#      lr:=tzrules[i];
#      lrw:=rules[i];
#      ch:=0;
#      w:=redwith(lr[2],t);
#      if w<>lr[2] then
#        if ch=0 then ch:=1;fi;
#        lr[2]:=w;
#        lrw[2]:=AssocWordByLetterRep(FamilyObj(rul[1]),w);
#      fi;
#      w:=redwith(lr[1],t);
#      if w<>lr[1] then
#        ch:=2;
#        lr[1]:=w;
#        lrw[2]:=AssocWordByLetterRep(FamilyObj(rul[1]),w);
#      fi;
#      if ch>0 then
#        RemoveSet(sel,i);
#        if lr[1]<>lr[2] then
#          if ch=2 and IsLessThanOrEqualUnder(ord,lrw[1],lrw[2]) then
#            lr:=Reversed(lr);
#            lrw:=Reversed(lrw);
#          fi;
#          Add(stack,[lr,lrw]);
#        fi;
#      fi;
#      
#    od;
#    if Length(sel)<Length(rules) then
#      # Print("kill ",Length(rules)-Length(sel)," to ",Length(stack),"\n");
#      rules:=rules{sel};
#      tzrules:=tzrules{sel};
#    fi;
#
#    Add(rules,rul);
#    Add(tzrules,t);
#
#    if Length(stack)>0 then
#      for i in stack do
#        # delayed add of changed old rules. Will not cause problems as
#        # stacks are only processed after new rule was added.
#        addrule(i[2]);
#      od;
#    fi;
#
  end;

  fam:=FamilyObj(One(h));
  fs:=HybridBits(h);
  domon:=Size(Source(fam!.fphom))=Size(fs.factor);

  if domon and
   Length(fam!.auts)<>Length(GeneratorsOfGroup(Range(fam!.fphom))) then
    Error("generator discrepancy");
  fi;

  if domon then
    kermon:=ShallowCopy(ConfluentMonoidPresentationForGroup(fs.ker));
    kermon.freegens:=FreeGeneratorsOfFpMonoid(Range(kermon.monhom));
    iso:=kermon!.fphom;

  else
    iso:=IsomorphismFpGroup(fs.ker);
  fi;

  kfp:=Range(iso);
  pcgs:=List(GeneratorsOfGroup(kfp),x->PreImagesRepresentative(iso,x));
  pres:=fam!.presentation;
  f:=FreeGroup(Length(fam!.auts)
       +Length(FreeGeneratorsOfFpGroup(kfp)));
  rels:=[];

  if domon<>false then
    fmon:=List(GeneratorsOfGroup(f),String);
    fmon:=Concatenation(List(fmon,x->[x,Concatenation(x,"^-1")]));
    fmon:=FreeMonoid(fmon);
    mhead:=GeneratorsOfMonoid(fmon){[1..2*(Length(fam!.auts))]};
    mtail:=GeneratorsOfMonoid(fmon){
      [2*(Length(fam!.auts))+1..Length(GeneratorsOfMonoid(fmon))]};
#    rules:=[];
#    tzrules:=[];

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
    head:=Concatenation(head+Maximum(tail),tail);
    ord:=WreathProductOrdering(fmon,head);
    kb:=CreateKnuthBendixRewritingSystem(FamilyObj(One(fmon/[])),ord);
    if AssertionLevel()<=2 then
      # assertion level <=2 so the auto tests will never trigger it
      Unbind(kb!.pairs2check);
    fi;
  fi;

  head:=GeneratorsOfGroup(f){[1..Length(fam!.auts)]};
  tail:=GeneratorsOfGroup(f){[Length(head)+1..Length(GeneratorsOfGroup(f))]};

  # relators of kernel
  for i in RelatorsOfFpGroup(kfp) do
    Add(rels,MappedWord(i,FreeGeneratorsOfFpGroup(kfp),tail));
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

      fi;
      addrule(nr);
    od;
  fi;

  if domon<>false then
    for i in RelationsOfFpMonoid(Range(kermon.monhom)) do
      addrule(List(i,x->MappedWord(x,kermon.freegens,mtail )));
    od;
  fi;

  # action on kernel
  for i in [1..Length(fam!.auts)] do
    # will the inverse of i actually live?
    img:=LetterRepAssocWord(mhead[2*i]);
    invliv:=ReduceLetterRepWordsRewSys(kb!.tzrules,img)=img;

    for j in [1..Length(pcgs)] do
      img:=ImagesRepresentative(fam!.auts[i],pcgs[j]);
      Add(rels,tail[j]^head[i]/MappedWord(ImagesRepresentative(iso,img),
        GeneratorsOfGroup(kfp),tail));
      if domon<>false then
        addrule([mtail[2*j-1]*mhead[2*i-1],
          mhead[2*i-1]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img))),kermon.freegens,mtail) ]);
        addrule([mtail[2*j]*mhead[2*i-1],
          mhead[2*i-1]*MappedWord(UnderlyingElement(
            ImagesRepresentative(kermon.monhom,
             ImagesRepresentative(iso,img^-1))),kermon.freegens,mtail) ]);

        # now map with inverse, unless it gets killed by rules
        if invliv then
          img:=PreImagesRepresentative(fam!.auts[i],pcgs[j]);
          addrule([mtail[2*j-1]*mhead[2*i],
            mhead[2*i]*MappedWord(UnderlyingElement(
              ImagesRepresentative(kermon.monhom,
              ImagesRepresentative(iso,img))),kermon.freegens,mtail) ]);
          addrule([mtail[2*j]*mhead[2*i],
            mhead[2*i]*MappedWord(UnderlyingElement(
              ImagesRepresentative(kermon.monhom,
              ImagesRepresentative(iso,img^-1))),kermon.freegens,mtail) ]);
        fi;
      fi;
    od;
  od;

  # tails
  for i in [1..Length(fam!.tails)] do
    Add(rels,MappedWord(pres.relators[i],GeneratorsOfGroup(pres.group),head)
      *MappedWord(ImagesRepresentative(iso,fam!.tails[i]),
        GeneratorsOfGroup(kfp),tail));
  od;

  f:=f/rels;
  head:=GeneratorsOfGroup(f){[1..Length(fam!.auts)]};
  tail:=GeneratorsOfGroup(f){[Length(head)+1..Length(GeneratorsOfGroup(f))]};
  gens:=[];
  for i in GeneratorsOfGroup(h) do
    if Length(head)>0 then
      Add(gens,MappedWord(i![1],GeneratorsOfGroup(pres.group),head)
        *MappedWord(ImagesRepresentative(iso,i![2]),GeneratorsOfGroup(kfp),tail));
    else
      Add(gens,MappedWord(ImagesRepresentative(iso,i![2]),GeneratorsOfGroup(kfp),tail));

    fi;
  od;
  gens:=Group(gens);

  if domon<>false then

    if IsBound(kb!.pairs2check) then
      rules:=StructuralCopy(Rules(kb));
      MakeConfluent(kb);
      Assert(3,Set(Rules(kb))=Set(rules));
    fi;

    rules:=Rules(kb);
    fmon:=FactorFreeMonoidByRelations(fmon,rules);

    nr:=KnuthBendixRewritingSystem(fmon,ord:isconfluent);
    nr!.reduced:=true;
Print("Have ",Length(rules)," rules\n");

    #i:=KnuthBendixRewritingSystem(fmon,ord);
    #MakeConfluent(i);
    #if Set(rules)<>Set(Rules(i)) then Error("enoi");else Print("hoo\n");fi;

    # make h generators corresponding to fp
    hgens:=[];
    for i in GeneratorsOfGroup(Range(fam!.fphom)) do
      Add(hgens,HybridGroupElement(fam,UnderlyingElement(i),fam!.normalone));
    od;
    for i in GeneratorsOfGroup(Range(iso)) do
      Add(hgens,HybridGroupElement(fam,fam!.factorone,
        PreImagesRepresentative(iso,i)));
    od;

    nr:=MakeFpGroupToMonoidHomType1(f,fmon);
    SetConfluentMonoidPresentationForGroup(gens,
      rec(fphom:=IdentityMapping(f),
          monhom:=nr,ordering:=ord));

    fphom:=GroupHomomorphismByImagesNC(h,f,
          hgens,GeneratorsOfGroup(f));
          #Concatenation(GeneratorsOfGroup(h),hgens),
          #Concatenation(GeneratorsOfGroup(gens),GeneratorsOfGroup(f)));
    SetIsBijective(fphom,true);
    SetConfluentMonoidPresentationForGroup(h,
      rec(fphom:=fphom,monhom:=nr,ordering:=ord));
    
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
  hom:=GroupHomomorphismByImagesNC(g,Group(module.generators),
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
            hom:=GroupHomomorphismByImagesNC(g,Group(module.generators),
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
    new:=GroupHomomorphismByImagesNC(fp,p,GeneratorsOfGroup(fp),
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
  if irr[1]<>GeneratorsOfGroup(a) then 
    # fix generators
    b:=[];
    for i in irr[2] do
      ext:=GroupHomomorphismByImagesNC(a,Group(i.generators),irr[1],
        i.generators);
      Add(b,GModuleByMats(List(GeneratorsOfGroup(a),x->ImagesRepresentative(ext,x)),
        i.field));
    od;
    irr:=[GeneratorsOfGroup(a),b];
  fi;
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
    cov:=WreathModuleCoverHybrid(a,i:dowords:=false);
    cov!.originalFactor:=a;
    b:=HybridBits(cov:dowords:=false);
    SetSize(cov,Size(b.factor)*Size(b.ker));
    b:=FamilyObj(One(cov));

    ker:=List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
      GeneratorsOfGroup(cov)));

    # now form normal closure
    kerpc:=Group(List(ker,x->x![2]),One(cov)![2]);
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
      Add(newq,[cov,ker,ext[Length(ext)],
        QuotientHybrid(cov,ker:dowords:=false)]);
    else
      Print("Cover of size ",Size(cov)," does not extend\n");
      Add(ext,0);
    fi;

  od;

  b:=List(newq,x->x[3]);
  Print("Now intersect covers, extend by ",ext," as ",b," to ",Sum(b),"\n");

  if Length(newq)=0 then return q;fi;

  cov:=newq[1][4];
  if IsHybridGroup(a) then cov!.originalFactor:=a; fi;
  for i in [2..Length(newq)] do
    b:=newq[i][4]; 
    if IsHybridGroup(a) then b!.originalFactor:=a; fi;
    cov:=SubdirectHybrid(cov,b:dowords:=false);
  od;

  fam:=FamilyObj(One(cov));
  if IsBound(fam!.quickermult) and fam!.quickermult<>fail then
    b:=HybridBits(cov:dowords:=false);
    SetSize(cov,Size(b.factor)*Size(b.ker));
    b:=Group(List(GeneratorsOfGroup(cov),fam!.quickermult));
    SetSize(b,Size(cov));
    cov:=b;
    fam:=FamilyObj(One(cov));
    if not IsBound(fam!.fphom) then
      if IsBound(FamilyObj(One(a))!.fphom) 
        and fam!.factgrp=Source(FamilyObj(One(a))!.fphom) then
        fam!.fphom:=FamilyObj(One(a))!.fphom;
      elif Size(fam!.factgrp)=1 then
        fam!.fphom:=GroupHomomorphismByImagesNC(fam!.factgrp,
          fam!.presentation.group, GeneratorsOfGroup(fam!.factgrp),
          List(GeneratorsOfGroup(fam!.factgrp),
            x->One(fam!.presentation.group))  );
      else
        Error("no fphom");
      fi;
    fi;
  fi;

  if IsHybridGroup(a) then cov!.originalFactor:=a; fi;
  b:=HybridBits(cov);

  Print("Recalculate module action\n");

  # recalculate module action
  kerpc:=Pcgs(b.ker);
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

  b:=GroupHomomorphismByImagesNC(G,cov,GeneratorsOfGroup(G),GeneratorsOfGroup(cov));
  SetImagesSource(b,cov);
  if ValueOption("irr")=fail then
    cov!.irreps:=[[p,[GeneratorsOfGroup(cov),irr]]];
  fi;
  return b;

end;

GeneralizedFibonacciGroup:=function(n,m,k)
local f,gens,rels,i;
  f:=FreeGroup(n,"x");
  gens:=GeneratorsOfGroup(f);
  gens:=Concatenation(gens,gens,gens);
  rels:=[];
  for i in [1..n] do
    Add(rels,gens[i]*gens[i+m]/gens[i+k]);
  od;
  return f/rels;
end;

CavicchioliGroup:=function(q)
local f,a,b,rels;
  f:=FreeGroup("a","b");
  a:=f.1;b:=f.2;
  rels:=[a*b*a^-2*b*a*b^-1,a*(b^-1*a^3*b^-1*a^-3)^q];
  return f/rels;
end;

SaveHybridGroup:=function(file,fam)
local pc,pcgs,auts,str,free,fp,mon,pres,t;
  PrintTo(file,"# Use `ReadAsFunction`\n",
    "local i,fam,type,pc,pcgs,auts,pres,free,fp,mon,fmon,ffam,mfam,mrels,gens,tails,t;\n");
  pc:=fam!.normal;
  pcgs:=FamilyPcgs(pc);
  auts:=List(fam!.auts,x->List(pcgs,y->ExponentsOfPcElement(pcgs,ImagesRepresentative(x,y))));


  str:=GapInputPcGroup(pc,"pc");
  AppendTo(file,str);
  AppendTo(file,"pcgs:=FamilyPcgs(pc);\n");
  AppendTo(file,"auts:=",auts,";\n");
  AppendTo(file,"auts:=",auts,";\n");
  AppendTo(file,"auts:=List(auts,x->GroupHomomorphismByImagesNC(pc,pc,pcgs,\n",
    "  List(x,y->PcElementByExponents(pcgs,y))));\n");

  pres:=fam!.presentation;
  free:=pres.group;
  AppendTo(file,"free:=FreeGroup(",List(GeneratorsOfGroup(free),String),");\n");
  AppendTo(file,"ffam:=FamilyObj(One(free));\n");

  AppendTo(file,"pres:=rec(group:=free,\n",
    "  killrelators:=List(",List(pres.killrelators,LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  relators:=List(",List(pres.relators,LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  prewords:=List(",List(pres.prewords,LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  monrulpos:=",pres.monrulpos,");\n");
  fp:=Range(fam!.fphom);
  AppendTo(file,"fp:=free/List(",List(RelatorsOfFpGroup(fp),LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x));\n");
  mon:=Range(fam!.monhom);
  AppendTo(file,"fmon:=FreeMonoid(",List(GeneratorsOfMonoid(FreeMonoidOfFpMonoid(mon)),String),");\n");
  AppendTo(file,"mfam:=FamilyObj(One(fmon));\n");
  AppendTo(file,"mrels:=List(",List(RelationsOfFpMonoid(mon),x->List(x,LetterRepAssocWord)),
      ",x->List(x,y->AssocWordByLetterRep(mfam,y)));\n");
  AppendTo(file,"mon:=fmon/mrels;\n");

  t:=List(fam!.tails,x->ExponentsOfPcElement(pcgs,x));
  AppendTo(file,"t:=",t,";\n");

  AppendTo(file,"fam:=NewFamily(\"Hybrid elements family\",IsHybridGroupElement);\n");
  AppendTo(file,"fam!.presentation:=pres;\n");
  AppendTo(file,"fam!.factgrp:=",fam!.factgrp,";\n");
  AppendTo(file,"fam!.fphom:=GroupHomomorphismByImagesNC(fam!.factgrp,fp,GeneratorsOfGroup(fam!.factgrp),\n",
    "    GeneratorsOfGroup(fp));\n");
  AppendTo(file,"fam!.monhom:=MakeFpGroupToMonoidHomType1(fp,mon);\n");
  AppendTo(file,"fam!.tzrules:=TranslatedMonoidRules(fam!.monhom);\n");
  AppendTo(file,"fam!.auts:=auts;\n");
  AppendTo(file,"fam!.autsinv:=List(auts,Inverse);\n");
  AppendTo(file,"fam!.factorone:=One(free);\n");
  AppendTo(file,"fam!.normalone:=One(pc);\n");
  AppendTo(file,"fam!.normal:=pc;\n");
  AppendTo(file,"fam!.wholeSize:=Size(fam!.factgrp)*Size(fam!.normal);\n");
  AppendTo(file,"HybridAutMats(fam);\n");
  AppendTo(file,"type:=NewType(fam,IsHybridGroupElementDefaultRep);\n");
  AppendTo(file,"fam!.defaultType:=type;\n");
  AppendTo(file,"SetOne(fam,HybridGroupElement(fam,fam!.factorone,fam!.normalone));\n");
  AppendTo(file,"gens:=[];\n");
  AppendTo(file,"for i in GeneratorsOfGroup(free) do\n");
  AppendTo(file,"Add(gens,HybridGroupElement(fam,i,fam!.normalone));\n");
  AppendTo(file,"od;\n");
  AppendTo(file,"for i in pcgs do\n");
  AppendTo(file,"Add(gens,HybridGroupElement(fam,fam!.factorone,i));\n");
  AppendTo(file,"od;\n");
  AppendTo(file,"tails:=[];\n");
  AppendTo(file,"for i in t do\n");
  AppendTo(file,"Add(tails,PcElementByExponents(pcgs,i));\n");
  AppendTo(file,"od;\n");
  AppendTo(file,"fam!.tails:=tails;\n");
  AppendTo(file,"gens:=Group(gens);\n");
  AppendTo(file,"fam!.wholeGroup:=gens;\n");
  AppendTo(file,"return gens;\n");
end;
