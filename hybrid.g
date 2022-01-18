# Code, accompanying the paper "Constructing Universal Covers of Finite
# Groups" by H. Dietrich and A. Hulpke, Hybrid group version
# (C) 2020 by the authors.
# This code requires GAP 4.11 or newer

# User functions:
#
# HybridGroupCocycle(cohomrecord,cocycle)
#
# WreathModuleCoverHybrid(H,module) constructs
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
  InstallTrueMethod(CanComputeFittingFree, IsHybridGroup);
  InstallTrueMethod( IsSubsetLocallyFiniteGroup, IsHybridGroupElementCollection );

InstallTrueMethod( IsGeneratorsOfMagmaWithInverses,
  IsHybridGroupElementCollection );
fi;

DeclareRepresentation("IsHybridGroupElementDefaultRep",
  IsPositionalObjectRep and IsHybridGroupElement,[]);

HybridGroupRuleIndex:=function(tzr,rule,s)
local l;
  l:=Length(rule);
  if s>l then
    return tzr.offset;
  elif s=l then
    return (rule[s]+tzr.offset)*tzr.doboff+tzr.offset;
  else
    return (rule[s]+tzr.offset)*tzr.doboff+tzr.offset+rule[s+1];
  fi;
end;

TranslatedMonoidRules:=function(monhom)
local fam,t,r,i,offset,deadend,dag,tt,w,a,j;
  fam:=FamilyObj(One(Range(monhom)));
  t:=List(RelationsOfFpMonoid(Range(monhom)),r->List(r,e->
    UnderlyingElement(PreImagesRepresentative(monhom,
      ElementOfFpMonoid(fam,e)))));

  t:=List(t,x->List(x,LetterRepAssocWord));
  offset:=1+Length(GeneratorsOfGroup(Source(monhom)));

  r:=rec(tzrules:=t,
         offset:=offset,
         doboff:=2*offset,
         starters:=List([1..4*offset^2],x->[]),
         freegens:=FreeGeneratorsOfFpMonoid(Range(monhom)),
         monhom:=monhom,
         monrules:=RelationsOfFpMonoid(Range(monhom)));
  for i in [1..Length(t)] do
    if Length(t[i,1])>0 then
      #Add(r.starters[t[i,1][1]+offset],[t[i,1],t[i,2],i]);
      Add(r.starters[HybridGroupRuleIndex(r,t[i,1],1)],[t[i,1],t[i,2],i]);
    fi;
  od;

  # construct a DAG for storing the rules
  # this assumes the rule set is reduced, i.e. no LHS is in another
  deadend:=ListWithIdenticalEntries(2*offset-1,fail);
  dag:=ShallowCopy(deadend);
  for i in [1..Length(t)] do
    tt:=t[i,1];
    w:=dag;
    for j in [1..Length(tt)] do
      a:=tt[j]+offset;
      if w[a]=fail then
        if j=Length(tt) then
          # store
          w[a]:=i;
        else
          w[a]:=ShallowCopy(deadend); # at least one symbol more
          w:=w[a];
        fi;
      elif IsList(w[a]) then w:=w[a]; # go to next letter
      else
        Error("rule subset of rule");
      fi;
    od;
  od;
  r.dag:=dag;

  return r;
end;

HybridGroupElement:=function(fam,top,bottom)
  # 3: inverse, 4: quickermult, 5: topinverse
  return Objectify(fam!.defaultType,[top,bottom,false,false,false]);
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

#InstallMethod(InverseOp,"hybrid group elements",
#  [IsHybridGroupElementDefaultRep],0,
#function(elm)
#local fam,inv,prd;
#  #cache inverses
#  if elm![3]<>false then
#    return elm![3];
#  else
#    fam:=FamilyObj(elm);
#     if IsBound(fam!.quickermult) and fam!.quickermult<>fail
#        and not ValueOption("notranslate")=true then
#      inv:=fam!.backtranslate(fam!.quickermult(elm)^-1);
#    else
#
#      # calculate a^-1*junk
#      # the collection is guaranteed to happen in the product routine
#      inv:=\*(HybridGroupElement(fam,InverseOp(elm![1]),fam!.normalone),
#        One(fam):notranslate);
#      # form (a,b)*(a^-1,1)=(1,c), then (a,b)^-1=(a^-1,c^-1)
#      prd:=elm*inv;
#      inv:=inv*HybridGroupElement(fam,fam!.factorone,InverseOp(prd![2]));
#      #if not IsOne(inv*elm) then Error("invbug");fi;
#    fi;
#
#    elm![3]:=inv;
#    return inv;
#  fi;
#
#end);

#  fam:=FamilyObj(a);
#  d:=HybridGroupElement(fam,a![1],fam!.normalone);
#  c:=HybridTopInverse(a)*(HybridGroupElement(fam,b![1],fam!.normalone)*d);
#  d:=HybridGroupElement(fam,fam!.factorone,b![2])*d;
#  c:=HybridGroupElement(fam,fam!.factorone,Inverse(a![2]))*(c*HybridGroupElement(fam,fam!.factorone,a![2]*(d![2]^a![2])));
#  return c;


BindGlobal("HybridTopInverse",function(elm)
local fam,inv,junk,let,i,j,ran,invs,prd,inliste,pos,wfam;
  if IsBound(elm![5]) and IsHybridGroupElement(elm![5]) then return elm![5];fi;
  fam:=FamilyObj(elm);
  if not IsBound(fam!.wrdinvs) then
    ran:=[1..Length(GeneratorsOfGroup(fam!.presentation.group))];
    wfam:=FamilyObj(One(fam!.presentation.group));
    # seed inverse list with length 1 (even do inverses, so they are there)
    invs:=[];
    for i in ran do
      for j in [i,-i] do
        let:=HybridGroupElement(fam,
          AssocWordByLetterRep(wfam,[j]),fam!.normalone);
        inv:=\*(HybridGroupElement(fam,InverseOp(let![1]),fam!.normalone),
          One(fam):notranslate);
        junk:=HybridGroupElement(fam,let![1],fam!.normalone)*inv;
        AddSet(invs,Immutable([[j],
          HybridGroupElement(fam,inv![1],inv![2]/junk![2])]));
      od;
    od;
    fam!.wrdinvs:=rec(ran:=ran,invs:=invs);
  else
    ran:=fam!.wrdinvs.ran;
    invs:=fam!.wrdinvs.invs;
  fi;

  # test and set position
  inliste:=function(l)
  local p;
    p:=PositionSorted(invs,Immutable([l]));
    if p>0 and p<=Length(invs) and invs[p][1]=l then
      pos:=p;
      return true;
    else
      return false;
    fi;
  end;

  pos:=fail;
  prd:=fail;
  let:=LetterRepAssocWord(elm![1]);
  i:=Length(let);
  while i>0 do
    # largest stored Endst"uck
    j:=0;
    while i-j>0 and inliste(let{[i-j..i]}) do
      j:=j+1;
    od;
    # shall we store one longer?
    if i-j-1>0 and j<4 and Length(invs)<10000 then
      inv:=invs[pos][2]*invs[PositionSorted(invs,[let{[i-j]}])][2];
      AddSet(invs,Immutable([let{[i-j..i]},inv]));
      inliste(let{[i-j..i]});
      j:=j+1;
    fi;

    inv:=invs[pos][2];
#Print(let{[i-j+1..i]},inv,"\n");
    if prd=fail then
      prd:=inv;
    else
      prd:=prd*inv;
    fi;
    i:=i-j;
  od;
  elm![5]:=prd;
  return prd;

end);

InstallMethod(InverseOp,"hybrid group elements",
  [IsHybridGroupElementDefaultRep],0,
function(elm)
local fam,inv,prd;
  fam:=FamilyObj(elm);
  #cache inverses
  if elm![3]<>false then
    return elm![3];
  elif IsOne(elm![1]) then
    inv:=HybridGroupElement(fam,fam!.factorone,Inverse(elm![2]));
  # keep the old code in fopr debugging purposes
  elif false then
     if IsBound(fam!.quickermult) and fam!.quickermult<>fail
        and not ValueOption("notranslate")=true then
      inv:=fam!.backtranslate(fam!.quickermult(elm)^-1);
    else

      # calculate a^-1*junk
      # the collection is guaranteed to happen in the product routine
      inv:=\*(HybridGroupElement(fam,InverseOp(elm![1]),fam!.normalone),
        One(fam):notranslate);
      # form (a,b)*(a^-1,1)=(1,c), then (a,b)^-1=(a^-1,c^-1)
      prd:=elm*inv;
      inv:=inv*HybridGroupElement(fam,fam!.factorone,InverseOp(prd![2]));
      #if not IsOne(inv*elm) then Error("invbug");fi;
    fi;

  else
    inv:=HybridGroupElement(fam,fam!.factorone,Inverse(elm![2]))
      *HybridTopInverse(elm);
  fi;
  elm![3]:=inv;
  return inv;

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

InstallMethod(Order,"hybrid group elts",true,
  [IsHybridGroupElementDefaultRep],0,
function(a)
local q,o,fam;
  fam:=FamilyObj(a);
  q:=MappedWord(a![1],GeneratorsOfGroup(fam!.presentation.group),
    GeneratorsOfGroup(fam!.factgrp));
  o:=Order(q);
  a:=a^o;
  if not IsOne(a![1]) then Error("order!");fi;
  return o*Order(a![2]);
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
#start1:=Runtime();
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
    fi;
    for i in f do
      if i>0 then m:=ImagesRepresentative(fam!.auts[i],m);
      else m:=ImagesRepresentative(fam!.autsinv[-i],m);fi;
    od;
    return m;
  end);

HybridOldMultRoutine:=function(a,b)
local fam,xc,y,tzrec,tzrules,starters,offset,x,has,p,sta,r,cancel,bd,popo,tail;

  fam:=FamilyObj(a);
  xc:=a![1]*b![1]; # top product
  y:=HybridGroupAutrace(fam,a![2],b![1])*b![2]; #bottom product

  # now reduce x with rules

  tzrec:=fam!.tzrules;
  starters:=tzrec.starters;
  offset:=tzrec.offset;
  tzrules:=tzrec.tzrules;
  x:=LetterRepAssocWord(xc);
  # collect from the left

  repeat
    has:=false;
    p:=1;
    while p<=Length(x) do
      sta:=starters[HybridGroupRuleIndex(tzrec,x,p)];
      r:=1;
      while r<=Length(sta) do
        if Length(sta[r,1])+p-1<=Length(x)
          # shortcut test for rest -- know first two work
          and ForAll([3..Length(sta[r,1])],y->x[p+y-1]=sta[r,1][y]) then

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

          p:=0; # as +1 is next
          has:=true;
          r:=Length(sta); # to exit sta loop
        fi;
        r:=r+1;
      od;
      p:=p+1;
    od;
  until has=false;

  x:=AssocWordByLetterRep(FamilyObj(fam!.factorone),x);
  return [x,y];
end;

#MyVerify:=function(fam,top,bot)
#local w,from,i,j;
#  w:=One(fam!.wholeGroup);
#  from:=1;
#  for i in bot do
#    for j in [from..i[1]] do
#      w:=w*g.(top[j]);
#    od;
#    w:=w*HybridGroupElement(fam,fam!.factorone,i[2]);
#    from:=i[1]+1;
#  od;
#  for j in [from..Length(top)] do
#    w:=w*g.(top[j]);
#  od;
#  Print("Verify: ",w,"\n");
#  return w;
#end;

InstallMethod(\*,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
local fam,rules,tzrec,r,i,p,has,x,y,tail,popo,tzrules,offset,bd,starters,
      dag,sta,cancel,xc,addbot,bot,sweep,botsh,pto,diff,muss,w,q;

  fam:=FamilyObj(a);

  if IsBound(fam!.quickermult) and fam!.quickermult<>fail
    and not ValueOption("notranslate")=true then
    return fam!.backtranslate(fam!.quickermult(a)*fam!.quickermult(b));
  fi;

  x:=LetterRepAssocWord(a![1]*b![1]);
  bot:=[]; # tail entries, *after* which position the tail bit happens.
  addbot:=function(pos,val)
  local p;
    p:=PositionSorted(bot,[pos]);
    if p<=Length(bot) and bot[p][1]=pos then
      val:=val*bot[p][2];
      if IsOne(val) then
        # cancellation -- kill
        bot:=Concatenation(bot{[1..p-1]},bot{[p+1..Length(bot)]});
        IsSSortedList(bot);
      else
        bot[p]:=Immutable([pos,val]);
      fi;
    else
      AddSet(bot,Immutable([pos,val]));
    fi;
  end;

  # move bottom elements out of range
  sweep:=function(from,to)
  local i,p,q,a;
    i:=1;
    while i<=Length(bot) do
      p:=bot[i][1];
      if p<from then
        i:=i+1;
      elif p>=to then
        i:=Length(bot)+1; # done, exit
      else
        # need to take out
        a:=bot[i][2];
        bot:=Concatenation(bot{[1..i-1]},bot{[i+1..Length(bot)]});
        # bump into another? Now i is the ext
        if i<=Length(bot) and bot[i][1]<to then
          q:=bot[i][1];
        else
          q:=to;
        fi;
        # move and enter, possibly changing next entry
        a:=HybridGroupAutrace(fam,a,x{[p+1..q]});
        addbot(q,a);
        # no i increment needed, as we deleted current one
      fi;
    od;
  end;

  # change all bot entries that are at `from' or later by `by`
  botsh:=function(from,by)
  local i;
    i:=1;
    while i<=Length(bot) do
      if bot[i][1]>=from then
        bot[i]:=Immutable([bot[i][1]+by,bot[i][2]]);
        # collision?
        if i>1 and bot[i][1]=bot[i-1][1] then
          bd:=[bot[i][1],bot[i-1][2]*bot[i][2]];
          bot:=Concatenation(bot{[1..i-2]},bot{[i+1..Length(bot)]});
          addbot(bd[1],bd[2]);
          i:=i-1;
        fi;
      fi;
      i:=i+1;
    od;
  end;

  if not IsOne(b![2]) then
    # do this first, since addbot moves in from the left
    addbot(Length(x),b![2]);
  fi;
  if not IsOne(a![2]) then
    if Length(x)=Length(a![1])+Length(b![1]) then
      # no cancellation -- just enter
      addbot(Length(a![1]),a![2]);
    else
      # move tail past b first, so it is out of the way of cancellation
      addbot(Length(x),HybridGroupAutrace(fam,a![2],b![1]));
    fi;
  fi;

#if ValueOption("old")<>true then muss:=\*(a,b:old);fi;
#if ValueOption("old")<>true and muss<>MyVerify(fam,x,bot:old) then

  tzrec:=fam!.tzrules;
  starters:=tzrec.starters;
  offset:=tzrec.offset;
  tzrules:=tzrec.tzrules;
  dag:=tzrec.dag;

  # collect from the left

  repeat
    has:=false;
    p:=1;
    while p<=Length(x) do
      # find the rule applying at the position in the dag
      w:=dag;
      q:=p;
      while IsList(w) and q<=Length(x) do
        w:=w[x[q]+offset];
        q:=q+1;
      od;
      if IsInt(w) then
        sta:=tzrules[w];

        # now we apply a rule

        pto:=p+Length(sta[1])-1;
        sweep(p-1,pto); # move out letters in the way

        # change stored indices as needed
        diff:=Length(sta[2])-Length(sta[1]);
        if diff<>0 then
          botsh(pto,diff);
        fi;

        tail:=x{[pto+1..Length(x)]};
        # do free cancellation, which does not involve tails
        cancel:=0;
        bd:=Length(sta[2]);if p-1<bd then bd:=p-1;fi;
        while cancel<bd and x[p-1-cancel]=-sta[2][1+cancel] do
          cancel:=cancel+1;
        od;
        if cancel>0 then
          p:=p-1; # end of old
          # first form the word with the to-cancel bit
          x:=Concatenation(x{[1..p]},sta[2]);
          # move out all bottoms in the cancellation range
          sweep(p-cancel+1,p+cancel);
          # reindex those after the cancellation
          botsh(p+cancel,-2*cancel);
          # cut out cancelled bit
          x:=Concatenation(x{[1..p-cancel]},x{[p+1+cancel..Length(x)]});
        else
          x:=Concatenation(x{[1..p-1]},sta[2]);
        fi;

        popo:=Position(fam!.presentation.monrulpos,w);
        if popo<>fail and not IsOne(fam!.tails[popo]) then
          # store tail
          addbot(Length(x),fam!.tails[popo]);
        fi;

        # do free cancellation, which does not involve tails
        cancel:=0;
        bd:=Length(tail);if Length(x)<bd then bd:=Length(x);fi;
        while cancel<bd and x[Length(x)-cancel]=-tail[1+cancel] do
          cancel:=cancel+1;
        od;
        if cancel>0 then
          p:=Length(x);
          # first form the word with the to-cancel bit
          x:=Concatenation(x,tail);
          # move out all bottoms in the cancellation range
          sweep(p-cancel+1,p+cancel);
          # reindex those after the cancellation
          botsh(p+cancel,-2*cancel);
          # cut out cancelled bit
          x:=Concatenation(x{[1..p-cancel]},x{[p+1+cancel..Length(x)]});
        else
          x:=Concatenation(x,tail);
        fi;

        p:=0; # as +1 is at end of loop
        has:=true;

      fi;

      p:=p+1;
    od;
  until has=false;
#Error("@",x,bot,"\n");
  sweep(0,Length(x)); # clean out all

  if Length(bot)>0 then
    if Length(bot)>1 then Error("sweeps?");fi;
    y:=bot[1][2];
  else
    y:=fam!.normalone;
  fi;

  x:=AssocWordByLetterRep(FamilyObj(fam!.factorone),x);

#p:=HybridOldMultRoutine(a,b);
#if ValueOption("old")=true then
#  x:=p[1];y:=p[2];
#elif x<>p[1] or y<>p[2] then Error("arithmetic error");x:=p[1];y:=p[2];fi;

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
    yinv:=y^-1;
    a:=yinv*h*y;
  fi;
  if t<>fail then
    a:=a*HybridGroupElement(fam,One(x![1]),HybridGroupAutrace(fam,t,y![1]));
  fi;
  return a;
end);

TC:=function(a,b)
local fam,ax,ay,bx,by,c;
  fam:=FamilyObj(a);
  ax:=HybridGroupElement(fam,a![1],fam!.normalone);
  bx:=HybridGroupElement(fam,b![1],fam!.normalone);
  ay:=HybridGroupElement(fam,fam!.factorone,a![2]);
  #by:=HybridGroupElement(fam,fam!.factorone,b![2]);
  c:=HybridGroupElement(fam,fam!.factorone,(ay*bx)![2]^b![2]);
  return Inverse(b)*ax*b*c;
end;

InstallMethod(\^,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(b,a)
local fam,c;
  fam:=FamilyObj(a);
  if IsOne(b![1]) then
    if not IsOne(a![1]) then
      if IsOne(a![2]) then
        c:=a;
      else
        c:=HybridGroupElement(fam,a![1],fam!.normalone);
      fi;
      b:=b*c;
    fi;
    b:=b![2]; # front stays the same and cancels off
    if not IsOne(a![2]) then
      b:=b^a![2];
    fi;
    return HybridGroupElement(fam,fam!.factorone,b);
  else
    return Inverse(a)*b*a;
  fi;
end);

InstallMethod(Comm,"hybrid group elements",IsIdenticalObj,
  [IsHybridGroupElementDefaultRep,IsHybridGroupElementDefaultRep],0,
function(a,b)
  # in experimenst this weird evaluation is faster
  return Inverse(a)*(Inverse(b)*a)*b;
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

    # transfer wreath ordering info
    if HasReducedConfluentRewritingSystem(Range(fam!.monhom)) then
      pres:=ReducedConfluentRewritingSystem(Range(fam!.monhom));
      pf:=OrderingOfRewritingSystem(pres);
      if HasLevelsOfGenerators(pf) then
        pf:=LevelsOfGenerators(pf);
        pf:=pf{[1..Length(GeneratorsOfMonoid(mon))]};
        pf:=pf-Minimum(pf)+1;
        pf:=WreathProductOrdering(FamilyObj(RelationsOfFpMonoid(mon)[1][1]),pf);
        pres:=KnuthBendixRewritingSystem(mon,pf:isconfluent);
        SetOrderingOfRewritingSystem(pres,pf);
        SetReducedConfluentRewritingSystem(mon,pres);
      fi;
    fi;

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

    a![4]:=b;
    return b;
  end;

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
    adf:=UnderlyingElement(ImagesRepresentative(r.fphom,gens[i]));
    b:=MappedWord(adf,fgens,GeneratorsOfGroup(prd){[1..Length(fgens)]});
    b:=HybridGroupElement(fam,b![1],a);
    Add(new,b);
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
  while Length(e)<lim and i<Length(e) do
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
  xker,xkerw,addker,dowords,ffam,of,sz,isorec;

  if HasSize(G) then 
    sz:=Size(G);
  else
    sz:=fail;
  fi;
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
  if sz=fail then sz:=Size(fam!.normal);
  else sz:=sz/Size(factor);fi;

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
    isorec:=rec(fphom:=iso,
       apply:=x->ImagesRepresentative(iso,x));
  elif true then
    iso:=IsomorphismFpGroup(factor);
    isorec:=rec(fphom:=iso,
       apply:=x->ImagesRepresentative(iso,x));
  else
    isorec:=ShallowCopy(ConfluentMonoidPresentationForGroup(factor));
    iso:=isorec.fphom;
    isorec.kb:=ReducedConfluentRewritingSystem(Range(isorec.monhom));
    isorec.fam:=FamilyObj(One(Range(isorec.monhom)));
    isorec.apply:=function(x)
      x:=ReducedForm(isorec.kb,UnderlyingElement(
        ImagesRepresentative(isorec.monhom,
	  ImagesRepresentative(isorec.fphom,x))));
      x:=ElementOfFpMonoid(isorec.fam,x);
      x:=PreImagesRepresentative(isorec.monhom,x);
      return x;
    end;
  fi;
  fp:=Range(iso);

  if dowords then
    addker:=function(w)
    local img,i,part;
      if Size(sub)=sz then return;fi; # not needed
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
    if Size(sub)<sz then
      j:=gfg[sel[i]]/MappedWord(UnderlyingElement(
        #ImagesRepresentative(iso,top[i])),
        isorec.apply(top[i])),
        FreeGeneratorsOfFpGroup(fp),map);
      addker(j);
      addker(gfg[sel[i]]^Order(top[i]));
    fi;
  od;

  if dowords and (IsPermGroup(factor) or IsPcGroup(factor))
    and Size(sub)<sz and Size(factor)>1 then

    # presentation
    j:=IsomorphismFpGroupByGenerators(factor,top);
    j:=Range(j);
    for i in RelatorsOfFpGroup(j) do
      if Size(sub)<sz then
        i:=MappedWord(i,FreeGeneratorsOfFpGroup(j),gfg{sel});
        addker(i);
      fi;
    od;
  fi;

  if dowords and IsBound(G!.originalFactor) and Size(sub)<sz then
    of:=HybridBits(G!.originalFactor);
    for i in of.wordskerpcgs do
      addker(MappedWord(i,of.freegens,gfg));
    od;
  fi;

  # evaluate relators
  if Size(sub)<sz then
    for i in List(RelatorsOfFpGroup(fp),
                      x->MappedWord(x,FreeGeneratorsOfFpGroup(fp),map)) do
      addker(i);
    od;
  fi;

  # short words
  if Size(sub)<sz and Length(sel)>0 then
    j:=ShortKerWords(fam,GeneratorsOfGroup(G){sel},gfg{sel},100);
    for i in j[2] do
      addker(i);
    od;
  fi;

  # now form normal closure
  i:=1;
  while i<=Length(ker) and Size(sub)<sz do
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
    #Print(List(kerw,Length)," vs ",List(i[2],Length),"\n");
  else
    i:=[CanonicalPcgsWrtFamilyPcgs(sub)];
  fi;

  sub:=Group(i[1],fam!.normalone);
  j:=rec(factor:=factor,
          ker:=sub,
	  apply:=isorec.apply,
          factoriso:=iso);
  if dowords then
    j.freegens:=gfg;
    j.wordsfreps:=map;
    j.kerpcgs:=i[1];
    sub:=List(map,
      x->MappedWord(x,gfg,GeneratorsOfGroup(G)));
    j.freps:=sub;
    # clean out kernel bits
    j.frepsfilter:=List(sub,x->HybridGroupElement(fam,x![1],
      SiftedPcElement(j.kerpcgs,x![2])));
    j.wordskerpcgs:=i[2];
  else
    j.freps:=map;
  fi;
  G!.hybridbits:=j;
  return j;
end;

InstallMethod(\in,"hybrid group",IsElmsColls,
  [IsHybridGroupElement,IsGroup],0,
function(elm,g)
local fam,bits,elq;
  fam:=FamilyObj(elm);
  if IsIdenticalObj(g,fam!.wholeGroup) or HasSize(g) and
    Size(g)=fam!.wholeSize then
    return true;
  fi;
  bits:=HybridBits(g);
  elq:=MappedWord(elm![1],
    GeneratorsOfGroup(fam!.presentation.group),
    GeneratorsOfGroup(fam!.factgrp));
  if not elq in bits.factor then return false;fi;
  if Length(bits.freps)>0 then
    # divide off possible nontrivial factor part
    elq:=ImagesRepresentative(bits.factoriso,elq);
    elq:=MappedWord(elq,GeneratorsOfGroup(Range(bits.factoriso)),
      bits.freps);
    elm:=elm/elq;
  fi;
  if not IsOne(elm![1]) then Error("weird!");fi;
  return IsOne(SiftedPcElement(CanonicalPcgs(bits.kerpcgs),elm![2]));
  #TryNextMethod();
end);

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
    new:=OwnHybrid(new);
    ShadowHybrid(FamilyObj(One(new)));
  fi;

  return new;

end;

BindGlobal("HybhomCachedProduct",function(hom,l)
local p,w,i;
  p:=PositionSorted(hom!.wordcache,Immutable([l]));
  if p<=Length(hom!.wordcache) and hom!.wordcache[p][1]=l then
    return hom!.wordcache[p][2];
  fi;
  p:=hom!.topho[3];
  w:=One(p[1]);
  for i in l do
    if i>0 then w:=w*p[i];
    else w:=w/p[-i];fi;
  od;
  AddSet(hom!.wordcache,Immutable([l,w]));
  return w;
end);

InstallMethod(ImagesRepresentative,"hybrid",FamSourceEqFamElm,
  [IsGroupGeneralMappingByImages,
    IsMultiplicativeElementWithInverse and IsHybridGroupElementDefaultRep],0,
function(hom,elm)
local src,mgi,fam,map,toppers,topi,ker,hb,r,a,topho,topdec,pchom,pre,sub,
      pcgs,sortfun,e,ro,i,nn,ao,pres,gens,prevs,rw,ri,split,lim;

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
            List(hb.wordsfreps,x->MappedWord(x,hb.freegens,mgi[2])),
	    hb.apply];

    hom!.topho:=topho;
    hom!.underlyingpchom:=pchom;
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
  #r:=ImagesRepresentative(topho[1],r);
  r:=topho[5](r);
  if not IsBound(hom!.wordcache) then
    hom!.wordcache:=[];
    hom!.lenlim:=First([10,9..1],x->Length(topho[2])^x<5*10^4);
  fi;
  if not IsBound(hom!.previouses) then hom!.previouses:=[]; fi;

  prevs:=hom!.previouses;
  i:=PositionProperty(prevs,x->x[1]=r);
  if i=fail then
    #rw:=MappedWord(Inverse(r),topho[2],topho[3]);
    split:=LetterRepAssocWord(UnderlyingElement(Inverse(r)));
    split:=List(
      List([1..QuoInt(Length(split)+hom!.lenlim-1,hom!.lenlim)],
	x->Intersection([1..Length(split)],
	  [(x-1)*hom!.lenlim+1..x*hom!.lenlim])),
	  x->split{x});
    rw:=List(split,x->HybhomCachedProduct(hom,x));
    rw:=Product(rw,One(Source(hom)));

    if Length(topho[2])=0 and IsOne(r) then
      ri:=One(Range(hom));
    else
      ri:=MappedWord(r,topho[2],topho[4]);
    fi;
    Add(prevs,[r,rw,ri]);
    if Length(prevs)>20 then
      for i in [1..20] do
        prevs[i]:=prevs[i+1];
      od;
      for i in [21..Length(prevs)] do Unbind(prevs[i]);od;
    fi;
  else
    rw:=prevs[i][2];
    ri:=prevs[i][3];
    if i<>Length(prevs) then 
      a:=prevs[i];
      prevs[i]:=prevs[Length(prevs)];
      prevs[Length(prevs)]:=a;
    fi;
  fi;

  a:=rw*elm;
  a:=ri*ImagesRepresentative(pchom,a![2]);

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

  addrule:=function(rul)
  local t;
    t:=List(rul,LetterRepAssocWord);
    AddRuleReduced(kb,t);
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
  if GeneratorsOfGroup(f)=gens then 
    gens:=f;
  else
    gens:=SubgroupNC(f,gens);
  fi;

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
local pc,pcgs,auts,str,free,fp,mon,pres,t,rws,ord;
  PrintTo(file,"# Use `ReadAsFunction`\n",
    "local i,fam,type,pc,pcgs,auts,pres,free,fp,mon,fmon,ffam,mfam,mrels,\n",
    "       gens,tails,t,ord,rws;\n");
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
#    "  killrelators:=List(",List(pres.killrelators,LetterRepAssocWord),
#      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  relators:=List(",List(pres.relators,LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  prewords:=List(",List(pres.prewords,LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x)),\n",
    "  monrulpos:=",pres.monrulpos,");\n");
  fp:=Source(fam!.monhom);
  AppendTo(file,"fp:=free/List(",List(RelatorsOfFpGroup(fp),LetterRepAssocWord),
      ",x->AssocWordByLetterRep(ffam,x));\n");
  mon:=Range(fam!.monhom);
  AppendTo(file,"fmon:=FreeMonoid(",List(GeneratorsOfMonoid(FreeMonoidOfFpMonoid(mon)),String),");\n");
  AppendTo(file,"mfam:=FamilyObj(One(fmon));\n");
  AppendTo(file,"mrels:=List(",List(RelationsOfFpMonoid(mon),x->List(x,LetterRepAssocWord)),
      ",x->List(x,y->AssocWordByLetterRep(mfam,y)));\n");
  AppendTo(file,"mon:=fmon/mrels;\n");

  if HasReducedConfluentRewritingSystem(mon) then
    rws:=ReducedConfluentRewritingSystem(mon);
    if Set(Rules(rws))=Set(RelationsOfFpMonoid(mon)) and
      (IsBound (rws!.ordering) or HasOrderingOfRewritingSystem(rws)) then
        if HasOrderingOfRewritingSystem(rws) then
          ord:=OrderingOfRewritingSystem(rws);
        else
          ord:=rws!.ordering;
        fi;
        if HasLevelsOfGenerators(ord) then
          AppendTo(file,"ord:=WreathProductOrdering(FamilyObj(One(fmon)),\n",
            LevelsOfGenerators(ord),");\n");
          AppendTo(file,"rws:=KnuthBendixRewritingSystem(mon,ord:isconfluent);\n",
          "SetReducedConfluentRewritingSystem(mon,rws);\n");
        fi;
    fi;
  fi;

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

# use easier pres. for factor
FpGroupHybridOtherFactor:=function(h,factormap)
local hgens,fam,fs,iso,kfp,pres,f,rels,head,tail,i,j,pcgs,gens,frank,
  fpre,frange,hpcgs,
  fmon,rules,mhead,mtail,kermon,img,nr,ord,w,k,tzrules,redwith,
  fphom,kb,invliv;

  fam:=FamilyObj(One(h));
  fs:=HybridBits(h);

  if fs.factor<>Source(factormap) then Error("factor bit wrong");fi;
  frange:=Range(factormap);
  fpre:=List(GeneratorsOfGroup(frange),x->
    ImagesRepresentative(fam!.fphom,PreImagesRepresentative(factormap,x)));

  fpre:=List(fpre,x->MappedWord(x,GeneratorsOfGroup(Range(fam!.fphom)),
    GeneratorsOfGroup(h){[1..Length(fam!.auts)]}));

  frank:=Length(fpre);

  iso:=IsomorphismFpGroup(fs.ker);

  kfp:=Range(iso);
  pcgs:=List(GeneratorsOfGroup(kfp),x->PreImagesRepresentative(iso,x));
  hpcgs:=List(pcgs,x->HybridGroupElement(fam,fam!.factorone,x));

  gens:=Concatenation(fpre,hpcgs);

  f:=FreeGroup(frank+Length(FreeGeneratorsOfFpGroup(kfp)));
  rels:=[];

  head:=GeneratorsOfGroup(f){[1..frank]};
  tail:=GeneratorsOfGroup(f){[Length(head)+1..Length(GeneratorsOfGroup(f))]};

  # relators of kernel
  for i in RelatorsOfFpGroup(kfp) do
    Add(rels,MappedWord(i,FreeGeneratorsOfFpGroup(kfp),tail));
  od;

  # action on kernel
  for i in [1..frank] do

    for j in [1..Length(pcgs)] do
      img:=hpcgs[j]^fpre[i];
      img:=img![2];
      Add(rels,tail[j]^head[i]/MappedWord(ImagesRepresentative(iso,img),
        GeneratorsOfGroup(kfp),tail));
    od;
  od;

  # tails
  for i in RelatorsOfFpGroup(frange) do
    img:=MappedWord(i,FreeGeneratorsOfFpGroup(frange),fpre)![2];

    Add(rels,MappedWord(i,FreeGeneratorsOfFpGroup(frange),head)/
      MappedWord(ImagesRepresentative(iso,img),
        GeneratorsOfGroup(kfp),tail));
  od;

  f:=f/rels;
  return f;
end;

InstallMethod(SmallGeneratingSet,"hybrid",
  [IsGroup and IsHybridGroupElementCollection],0,
function(sub)
local fam,a,b,l,p,hb,sr,e,i,img;
  fam:=FamilyObj(One(sub));
  a:=Filtered(GeneratorsOfGroup(sub),x->not IsOne(x![1]));
  b:=ShallowCopy(a);
  l:=Length(a);
  p:=l;
  hb:=HybridBits(sub);
  sr:=TrivialSubgroup(hb.ker);
  while Size(sr)<Size(hb.ker) do
    e:=First(CanonicalPcgs(hb.kerpcgs),x->not x in sr);
    sr:=ClosureGroup(sr,e);
    e:=HybridGroupElement(fam,fam!.factorone,e);
    Add(a,e);
    Add(b,e);
    while p<Length(b) do
      p:=p+1;
      e:=b[p];
      for i in [1..l] do
        img:=e^a[i];
        if not img![2] in sr then
          Add(b,img);
          sr:=ClosureGroup(sr,img![2]);
        fi;
      od;
    od;
  od;
  return a;
end);


InstallMethod(FittingFreeLiftSetup,"hybrid",
  [IsGroup and IsHybridGroupElementCollection],0,
function(g)
local fam,b,geni,fmap,nat,dep,oc,iso,kb,mfam,pc,a,ser,premap,prerep,frad,ffh,
  fc,fcr,nc;
  fam:=FamilyObj(One(g));
  b:=HybridBits(g);
  # can we used induced form?
  if Size(b.ker)=Size(fam!.normal) and Size(RadicalGroup(b.factor))=1 then
    geni:=List(GeneratorsOfGroup(g),x->x![1]);
    geni:=List(geni,x->MappedWord(x,GeneratorsOfGroup(fam!.presentation.group),
      GeneratorsOfGroup(fam!.factgrp)));
    kb:=ReducedConfluentRewritingSystem(Range(fam!.monhom));;
    mfam:=FamilyObj(One(Range(fam!.monhom)));;
    nat:=GroupHomomorphismByFunction(g,fam!.factgrp,
      x->MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),
        GeneratorsOfGroup(fam!.factgrp)),false,
      function(elm)
      local w;
        w:=ImagesRepresentative(fam!.fphom,elm);
        w:=ImagesRepresentative(fam!.monhom,w);
        w:=ReducedForm(kb,UnderlyingElement(w));
        w:=ElementOfFpMonoid(mfam,w);
        w:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,w));
        return HybridGroupElement(fam,w,fam!.normalone);
      end);

    SetMappingGeneratorsImages(nat,[GeneratorsOfGroup(g),geni]);

    oc:=CanonicalPcgs(b.kerpcgs);
    pc:=List(oc,x->HybridGroupElement(fam,fam!.factorone,x));
    a:=List(GeneratorsOfGroup(g),x->GroupHomomorphismByImagesNC(b.ker,b.ker,
      oc,List(pc,y->(y^x)![2])));
    ser:=InvariantElementaryAbelianSeries(b.ker,a);
    a:=List(ser,InducedPcgsWrtFamilyPcgs);
    a:=List([2..Length(a)],x->a[x-1] mod a[x]);
    if Concatenation(a)<>oc then
      Error("not natural depths");
    fi;
    dep:=List(a,x->DepthOfPcElement(FamilyPcgs(b.ker),x[1]));
    Add(dep,Length(pc)+1);
    pc:=PcgsByPcSequence(fam,pc);
    SetRelativeOrders(pc,RelativeOrders(oc));
    SetIndicesEANormalSteps(pc,dep);
    pc!.underlying:=oc;
    pc!.fmap:=fail;
    a:=SubgroupByPcgs(g,pc);
    SetKernelOfMultiplicativeGeneralMapping(nat,a);

    iso:=GroupHomomorphismByFunction(a,b.ker,
        x->x![2],x->HybridGroupElement(fam,fam!.factorone,x));
    iso!.sourcePcgs:=pc;
  else

    geni:=List(GeneratorsOfGroup(g),x->x![1]);
    geni:=List(geni,x->MappedWord(x,GeneratorsOfGroup(fam!.presentation.group),
      GeneratorsOfGroup(fam!.factgrp)));

    if Size(b.ker)=Size(fam!.normal) then
      kb:=ReducedConfluentRewritingSystem(Range(fam!.monhom));;
      mfam:=FamilyObj(One(Range(fam!.monhom)));;
      # preimage representatives are obtained by simply writing the factor
      # word with a 1-tail
      prerep:=function(elm)
      local w;
        w:=ImagesRepresentative(fam!.fphom,elm);
        w:=ImagesRepresentative(fam!.monhom,w);
        w:=ReducedForm(kb,UnderlyingElement(w));
        w:=ElementOfFpMonoid(mfam,w);
        w:=UnderlyingElement(PreImagesRepresentative(fam!.monhom,w));
        return HybridGroupElement(fam,w,fam!.normalone);
      end;
    else
      premap:=GroupHomomorphismByImagesNC(b.factor,g,geni,GeneratorsOfGroup(g));
      prerep:=elm->ImagesRepresentative(premap,elm);
    fi;

    fmap:=GroupHomomorphismByFunction(g,b.factor,
      x->MappedWord(x![1],GeneratorsOfGroup(fam!.presentation.group),
        GeneratorsOfGroup(fam!.factgrp)),false,prerep);
    SetMappingGeneratorsImages(fmap,[GeneratorsOfGroup(g),geni]);

    frad:=RadicalGroup(b.factor);
    if Size(frad)=1 then
      nat:=fmap;
    else
      ffh:=NaturalHomomorphismByNormalSubgroupNC(b.factor,frad);
      nat:=fmap*ffh;
    fi;

    # pcgs in kernel
    oc:=CanonicalPcgs(b.kerpcgs);
    pc:=List(oc,x->HybridGroupElement(fam,fam!.factorone,x));
    if Size(b.ker)>1 then
      a:=List(GeneratorsOfGroup(g),x->GroupHomomorphismByImagesNC(b.ker,b.ker,
      oc,List(pc,y->(y^x)![2])));
      ser:=InvariantElementaryAbelianSeries(b.ker,a);
      a:=List(ser,CanonicalPcgsWrtFamilyPcgs);
      a:=List([2..Length(a)],x->a[x-1] mod a[x]);
      if Concatenation(a)<>oc then
        Error("not natural depths");
      fi;
    else
      a:=oc;
    fi;

    dep:=List(a,x->DepthOfPcElement(FamilyPcgs(b.ker),x[1]));
    Add(dep,Length(pc)+1);

    if Size(frad)>1 then
      # combine with Pcgs on top
      fc:=Pcgs(frad);
      dep:=dep+Length(fc);
      a:=List(GeneratorsOfGroup(b.factor),
        x->GroupHomomorphismByImagesNC(frad,frad,fc,List(fc,y->(y^x))));
      ser:=InvariantElementaryAbelianSeries(frad,a);
      a:=List(ser,x->CanonicalPcgs(InducedPcgs(fc,x)));
      a:=List([2..Length(a)],x->a[x-1] mod a[x]);
      if Concatenation(a)<>fc then
        fc:=PcgsByPcSequence(FamilyObj(One(frad)),Concatenation(a));
      fi;
      fcr:=List(fc,x->PreImagesRepresentative(fmap,x));
      nc:=pc;
      pc:=PcgsByPcSequenceCons( IsPcgsDefaultRep,IsPcgs and IsUnsortedPcgsRep,
                  fam, Concatenation(fcr,nc),[] );
      pc!.fmap:=fmap;
      pc!.factorpc:=fc;
      pc!.fcreps:=fcr;
      pc!.normalpc:=oc;
      SetRelativeOrders(pc,
        Concatenation(RelativeOrders(fc),RelativeOrders(oc)));
      if ForAll(RelativeOrders(pc),IsPrimeInt) then
        SetIsPrimeOrdersPcgs(pc,true);
      fi;
      dep:=Concatenation(List(a,x->DepthOfPcElement(fc,x[1])),dep);
      SetIndicesEANormalSteps(pc,dep);
      oc:=PcGroupWithPcgs(pc);
      iso:=GroupHomomorphismByImagesNC(SubgroupNC(g,pc),oc,pc,FamilyPcgs(oc));

    else
      pc:=PcgsByPcSequence(fam,pc);
      SetRelativeOrders(pc,RelativeOrders(oc));
      SetIndicesEANormalSteps(pc,dep);
      pc!.underlying:=oc;
      pc!.fmap:=fail;
      iso:=GroupHomomorphismByFunction(a,b.ker,
          x->x![2],x->HybridGroupElement(fam,fam!.factorone,x));
      iso!.sourcePcgs:=pc;
    fi;

    a:=SubgroupByPcgs(g,pc);
    SetKernelOfMultiplicativeGeneralMapping(nat,a);

  fi;
  a:=rec(depths:=dep,
    factorhom:=nat,
    pcgs:=pc,
    radical:=a);
  if iso<>fail then a.pcisom:=iso;fi;
  return a;
end);

InstallMethod( ExponentsOfPcElement, "hybrid", IsCollsElms,
      [ IsPcgs and IsHybridGroupElementCollection, IsHybridGroupElement ], 0,
function(pcgs,elm)
local a;
  if not IsBound(pcgs!.fmap) then
    TryNextMethod(); # built differently
  elif pcgs!.fmap=fail then
    return ExponentsOfPcElement(pcgs!.underlying,elm![2]);
  else
    a:=ExponentsOfPcElement(pcgs!.factorpc,
      ImagesRepresentative(pcgs!.fmap,elm));
    # divide off what the factor reps give
    elm:=LeftQuotient(LinearCombinationPcgs(pcgs!.fcreps,a),elm);
    if not IsOne(elm![1]) then Error("not clean");fi;
    Append(a,ExponentsOfPcElement(pcgs!.normalpc,elm![2]));
    return a;
  fi;
end);

InstallMethod(Random,"hybrid groups",true,[IsHybridGroup],0,
function(G)
local ffs,r;
  ffs:=FittingFreeLiftSetup(G);
  if Size(Image(ffs.factorhom))>1 then
    r:=PreImagesRepresentative(ffs.factorhom,Random(Image(ffs.factorhom)));
  else
    r:=One(G);
  fi;
  return r*PreImagesRepresentative(ffs.pcisom,Random(Image(ffs.pcisom)));
end);

InstallMethod(NaturalHomomorphismByNormalSubgroupOp,
  "hybrid groups",IsIdenticalObj,[IsHybridGroup,IsHybridGroup],0,
function(G,N)
local Q,fam,ffs;
  ffs:=FittingFreeSubgroupSetup(G,N);
  if N=ffs.parentffs.radical then
    return ffs.parentffs.factorhom;
  elif Length(ffs.pcgs)=Length(ffs.parentffs.pcgs) then
    Q:=ffs.parentffs.factorhom*NaturalHomomorphismByNormalSubgroup(Image(ffs.parentffs.factorhom,G),
      Image(ffs.parentffs.factorhom,N));
    return AsGroupGeneralMappingByImages(Q);
  else
    #T use split rep for factor
    Error("other nathom");
    TryNextMethod();
  fi;
end);

DeclareRepresentation("IsRightTransversalHybridGroupRep",IsRightTransversalRep,
    []);

InstallMethod(RightTransversal,"hybrid groups",IsIdenticalObj,
  [IsHybridGroup,IsHybridGroup],0,
function(G,S)
local fam,fg,fs,nat,nag,nas,a,qg,qs,qt,qtr,kt,pci,t;
  fam:=FamilyObj(One(G));
  fg:=FittingFreeSubgroupSetup(fam!.wholeGroup,G);
  fs:=FittingFreeSubgroupSetup(fam!.wholeGroup,S);
  nat:=fg.parentffs.factorhom;
  a:=List(GeneratorsOfGroup(G),x->ImagesRepresentative(nat,x));
  qg:=SubgroupNC(Range(nat),a);
  nag:=GroupHomomorphismByImagesNC(G,qg,GeneratorsOfGroup(G),a);

  a:=List(GeneratorsOfGroup(S),x->ImagesRepresentative(nat,x));
  qs:=SubgroupNC(Range(nat),a);
  nas:=GroupHomomorphismByImagesNC(S,qs,GeneratorsOfGroup(S),a);

  qt:=RightTransversal(qg,qs);
  qtr:=List(qt,x->PreImagesRepresentative(nag,x));
  pci:=fg.parentffs.pcisom;
  kt:=RightTransversal(Image(pci,fg.ker),Image(pci,fs.ker));

  t := Objectify( NewType( FamilyObj( G ),
                               IsList and IsDuplicateFreeList
                           and IsRightTransversalHybridGroupRep ),
          rec( group :=G,
            subgroup :=S,
            efam:=fam,
            nat:=nat,
            nag:=nag,
            nas:=nas,
            qt:=qt,
            qtr:=qtr,
            kt:=kt,
            coe:=[Length(qt),Length(kt)]
	    ));
  return t;
end);

InstallMethod(\[\],"for hybrid transversals",true,
    [ IsList and IsRightTransversalHybridGroupRep, IsPosInt ],0,
function(t,num)
local fam,c;
  fam:=t!.efam;
  c:=CoefficientsMultiadic(t!.coe,num-1)+1;
  return HybridGroupElement(fam,fam!.factorone,t!.kt[c[2]])*t!.qtr[c[1]];
end );

BindGlobal("HybTransPos",function(t,elm,cano)
local a,c;
  a:=ImagesRepresentative(t!.nat,elm);
  c:=PositionCanonical(t!.qt,a);
  if c=fail then return fail;fi;
  a:=a/t!.qt[c]; # factor elm
  elm:=elm/t!.qtr[c];
  a:=PreImagesRepresentative(t!.nas,a); # subgroup coset rep
  elm:=LeftQuotient(a,elm); # mult. by subgroup element to kill in factor, 
  # coset remains the same
  if not IsOne(elm![1]) then return fail;fi;
  a:=PositionCanonical(t!.kt,elm![2]);
  if a=fail then return fail;fi;
  if cano=false and elm<>t!.kt[a] then return fail;fi;
  return (c-1)*Length(t!.kt)+a;
end);

InstallMethod(PositionCanonical,"hybrid transversal",IsCollsElms,
    [ IsList and IsRightTransversalHybridGroupRep,
    IsMultiplicativeElementWithInverse ],0,
function(t,elm)
  return HybTransPos(t,elm,true);
end);

InstallMethod(Position,"hybrid transversal",IsCollsElms,
    [ IsList and IsRightTransversalHybridGroupRep,
    IsMultiplicativeElementWithInverse ],0,
function(t,elm)
  return HybTransPos(t,elm,false);
end);
