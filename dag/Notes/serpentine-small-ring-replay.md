---
title: Reproduce native small-ring bank and product transitions
refs: [note:serpentine-small-ring-issuer, definition:SerpentineBankMachine]
tags: [reproducibility, ring-lwe]
---

Compile the two C++17 interpreters with optimization. Run the individual Lean exporter with degree, mode 0 or 1, and table filename; its interpreter takes degree, mode, table, and row count. Run the bank Lean exporter with degree and table name; its interpreter takes degree, row count, pool count, mask count and the table name. The test fixtures use 1024/548/171/43 and 1024/337/171/43 for the bank, and 1024/86 in product mode. The external interpreter decodes the transition words from the actual registered machines. It samples a fixed reproducible coin tape for test purposes. The issuer itself uses the core fair coin.

### RowTable.lean

```lean
import Definitions.Def_SerpentineRowMachine
open SerpentineRing

def main (args : List String) : IO Unit := do
  let n:=(args[0]?.bind String.toNat?).getD 4
  let issue:=args[1]? == some "1"
  let name:=args[2]?.getD "table234.bin"
  let M:=machine n 1 issue
  let h←IO.FS.Handle.mk name .write
  for q in [:M.states] do
    let mut buf:=ByteArray.empty
    for i in [:3] do
      for a in [:3] do
        for k in [:3] do
          for c in [:2] do
            let tok:=fun j : Nat => if j==0 then none else some (j==2)
            match M.machine.tr ⟨q%M.states,Nat.mod_lt _ (Fin.pos M.machine.initial)⟩ (tok i)
                (fun j=> if j.val==0 then tok a else tok k) Fin.elim0 (c==1) with
            | .query v _ => nomatch v
            | .step v _ _ =>
              let dir:=fun (d : SignType) => match d with | .neg=>0 | .zero=>1 | .pos=>2
              let wr:=fun (w : Option (Option Bool)) => match w with | none=>0 | some none=>1 | some (some false)=>2 | some (some true)=>3
              let (aw,ad):=v.workTapes ⟨0, by change 0 < 2; decide⟩
              let (kw,kd):=v.workTapes ⟨1, by change 1 < 2; decide⟩
              let out:=match v.output with | none=>0 | some false=>1 | some true=>2
              let z:=(v.state.map (·.val)).getD M.states + 2^16*dir v.inputTape+2^18*dir ad+2^20*dir kd+2^22*wr aw+2^24*wr kw+2^26*out
              for j in [:4] do buf:=buf.push ((z/256^j)%256).toUInt8
    h.write buf
  IO.println (M.states,M.time,M.descLen)
```

### RowReplay.cpp

```cpp
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**v){
 int n=stoi(v[1]),sam=stoi(v[2]),rows=stoi(v[4]),w=4*n,db=6*w+4,fb=db+2720,tb=fb+576,stop=tb+2;
 vector<uint32_t> tr(stop*54);ifstream file(v[3],ios::binary);assert(file.read((char*)tr.data(),4*tr.size()));
 vector<int> input,outs,as(2*w+12),ks(2*w+12);
 mt19937 gen(234+rows);vector<vector<int>> keys(rows,vector<int>(n)),terms=keys,heads=keys,errs=keys;
 for(int r=0;r<rows;r++)for(auto ptr:{&keys[r],&terms[r]})for(auto&x:*ptr){x=gen()%16;for(int i=0;i<4;i++)input.push_back(1+((x>>i)&1));}
 int ah=3,kh=3,ip=0,q=0,j=0,row=0;long long tm=0;
 while(q!=stop){int coin=gen()&1;
   if(sam && q>=4*w && q<6*w && (q%2)){int i=(q-4*w)/2;heads.at(row)[i/4]|=coin<<(i%4);}
   if(sam && q>=fb && q<tb){int p=(q-fb)%12;if(p<2)errs.at(row)[j]+=p?-coin:coin;if(p==11 && ++j==n){row++;j=0;}}
   int inp=ip<int(input.size())?input[ip]:0;
   auto z=tr.at((((q*3+inp)*3+as.at(ah))*3+ks.at(kh))*2+coin);
   int aw=(z>>22)&3,kw=(z>>24)&3,out=(z>>26)&3;
   if(aw)as[ah]=aw-1;if(kw)ks[kh]=kw-1;if(out)outs.push_back(out-1);
   ip+=int((z>>16)&3)-1;ah+=int((z>>18)&3)-1;kh+=int((z>>20)&3)-1;q=z&65535;
   assert(++tm<=1LL*rows*(8*w+4+n*(w+13))+1);
 }
 vector<int> expected;
 for(int r=0;r<rows;r++){auto& a=sam?heads[r]:terms[r];auto& k=keys[r];vector<int> b(n);
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)b[(i+j)%n]+=(i+j>=n?-1:1)*a[i]*k[j];
 if(sam){for(int i=0;i<n;i++)b[i]+=errs[r][i]+terms[r][i];for(int x:a)for(int t=0;t<4;t++){expected.push_back(1);expected.push_back((x>>t)&1);}}
 for(int x:b)for(int t=0;t<4;t++){if(sam)expected.push_back(1);expected.push_back(((x%16+16)%16>>t)&1);}
 }
 if(sam)expected.push_back(0);
 if(outs!=expected){cerr<<"wrong length "<<outs.size()<<" expected "<<expected.size()<<"\n";return 2;}
 cout<<"degree "<<n<<" issue "<<sam<<" rows "<<rows<<" output "<<outs.size()<<" ticks "<<tm<<" clock "<<1LL*rows*(8*w+4+n*(w+13))+1<<"\n";
}
```

### BankTable.lean

```lean
import Definitions.Def_SerpentineBankMachine
def main (args : List String) : IO Unit := do
  let n:=(args[0]?.bind String.toNat?).getD 4
  let name:=args[1]?.getD "bank234.tab"
  let M:=SerpentineBank.machine n 548 171 8192
  let h←IO.FS.Handle.mk name .write
  for q in [:M.states] do
    let mut buf:=ByteArray.empty
    for i in [:3] do
      for a in [:3] do
        for k in [:3] do
          for p in [:3] do
            for c in [:2] do
              let tok:=fun j : Nat => if j==0 then none else some (j==2)
              match M.machine.tr ⟨q%M.states,Nat.mod_lt _ (Fin.pos M.machine.initial)⟩ (tok i)
                  (fun j=> if j.val==0 then tok a else if j.val==1 then tok k else tok p) Fin.elim0 (c==1) with
              | .query v _ => nomatch v
              | .step v _ _ =>
                let dir:=fun (d : SignType) => match d with | .neg=>0 | .zero=>1 | .pos=>2
                let wr:=fun (w : Option (Option Bool)) => match w with | none=>0 | some none=>1 | some (some false)=>2 | some (some true)=>3
                let (aw,ad):=v.workTapes ⟨0,by change 0<3;decide⟩
                let (kw,kd):=v.workTapes ⟨1,by change 1<3;decide⟩
                let (pw,pd):=v.workTapes ⟨2,by change 2<3;decide⟩
                let out:=match v.output with | none=>0 | some false=>1 | some true=>2
                let z:=(v.state.map (·.val)).getD M.states + 2^17*dir v.inputTape+2^19*dir ad+2^21*dir kd+2^23*dir pd+2^25*wr aw+2^27*wr kw+2^29*wr pw+2^31*out
                for j in [:5] do buf:=buf.push ((z/256^j)%256).toUInt8
    h.write buf
  IO.println (M.states,M.time,M.descLen)
```

### BankReplay.cpp

```cpp
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct Row{int a,b,op;};
int main(int argc,char**argv){
 int n=stoi(argv[1]),rows=stoi(argv[2]),count=stoi(argv[3]),masks=stoi(argv[4]),w=4*n;
 int ar=15+11*w+4+7,db=6*w+4,fb=db+2720,tb=fb+576,stop=ar+tb+2;
 vector<uint64_t> tr(stop*162);ifstream table(argv[5],ios::binary);for(auto &t:tr){unsigned char buf[5];assert(table.read((char*)buf,5));for(int i=0;i<5;i++)t|=uint64_t(buf[i])<<(8*i);}
 mt19937 gen(234);vector<int> in,output,as(8+w*count),ks(8+2*w),pk(8+2*w*rows);
 auto cmd=[&](int c){for(int i=3;i>=0;i--)in.push_back(1+((c>>i)&1));};
 int pos=0;auto get=[&](int k,int op){while(pos>k){cmd(2);--pos;}while(pos<k){cmd(3);++pos;}cmd(op);pos++;};
 vector<Row> R;int pubs=13;
 for(int i=0;i<pubs;i++)cmd(9+(i%2));
 for(int i=0;i<count;i++){cmd(i<count-masks?0:1);pos++;}
 get(0,7);get(1,7);
 for(int i=0;i<rows;i++){
  int src=(i/2)%max(1,count-masks), dst=(src+3)%(count-masks),op=i%2?4:5;
  if(rows==548 && count==171 && masks==43) {
   if(i<504){int e=i/2,l=e/6;src=e/3;dst=e%3==2?84+l:2*((l+1)%42)+e%3;op=i%2?4:5;}
   else{int t=i-504;src=84+t;dst=128+(t<42?t+1:0);op=t==43?4:6;}
  }else if(i%7==6){dst=count-masks+(i%masks);op=(i%2==1)?6:4;}
  get(src,4);get(dst,op);R.push_back({src,dst,op});
 }
 cmd(8);vector<vector<int>> key(count,vector<int>(n)),head(rows,vector<int>(n)),noise=head;
 int a=3,k=3,p=3,ip=0,q=0,row=0,j=0,num=0;long long ticks=0;
 while(q!=stop){int c=gen()&1;
   if(q>=15&&q<15+2*w){int idx=(q-15)%w,mask=(q-15)/w;key.at(num)[idx/4]|=int(c&&(!mask||idx==3))<<(idx%4);if(idx+1==w)num++;}
   int z=q-ar;if(z>=4*w&&z<6*w&&z%2){int i=(z-4*w)/2;head.at(row)[i/4]|=c<<(i%4);}
   if(z>=fb&&z<tb){int s=(z-fb)%12;if(s<2)noise.at(row)[j]+=s?-c:c;if(s==11&&++j==n){++row;j=0;}}
   int inp=ip<int(in.size())?in[ip]:0;
   uint64_t st=tr.at(((((q*3+inp)*3+as.at(a))*3+ks.at(k))*3+pk.at(p))*2+c);
   auto set=[&](int& x,int sh){int t=(st>>sh)&3;if(t)x=t-1;};set(as[a],25);set(ks[k],27);set(pk[p],29);
   int out=(st>>31)&3;if(out)output.push_back(out-1);
   auto move=[&](int sh){return int((st>>sh)&3)-1;};ip+=move(17);a+=move(19);k+=move(21);p+=move(23);
   q=st&131071;assert(++ticks<4000000000LL);
 }
 vector<int> expected;auto append=[&](int b){expected.push_back(1);expected.push_back(b);};
 auto push=[&](int x){for(int i=0;i<4;i++)append((x>>i)&1);};
 for(int i=0;i<pubs;i++)append(i%2);for(int i=0;i<2;i++)for(int x:key[i])push(x);
 for(int r=0;r<rows;r++){vector<int> b=noise[r];for(int x:head[r])push(x);
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)b[(i+j)%n]+=(i+j>=n?-1:1)*head[r][i]*key[R[r].a][j];
  for(int i=0;i<n;i++){int off=key[R[r].b][i];if(R[r].op==5)off=4*off;if(R[r].op==6&&i==0)off^=8;push((b[i]+off+16*65536)%16);}}
 expected.push_back(0);assert(num==count&&row==rows&&ip==int(in.size()));
 if(expected!=output){cerr<<"mismatch "<<expected.size()<<" "<<output.size()<<"\n";return 2;}
 cout<<"degree="<<n<<" rows="<<rows<<" shared words="<<count<<" programBits="<<in.size()<<" outputBits="<<output.size()<<" steps="<<ticks<<"\n";
}
```

### CheckAddresses.py

```python
from random import Random
def positions(n):
    k=4*n+3
    for j in range(n):
        step=1 if j%2==0 else -1
        for i in (range(n) if step==1 else reversed(range(n))):
            for bit in (range(4) if step==1 else reversed(range(4))):
                assert k//4-n==j-i and k%4==3-bit
                k-=step
        assert (k==8*n)==(j==n-1)
        k+=5 if step==1 else 3
for n in [2,4,6,8,32,1024]:positions(n)
print('All packed key and header head positions match the signed convolution indices.')
```
