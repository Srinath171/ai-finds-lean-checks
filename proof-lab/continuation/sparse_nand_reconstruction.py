"""Bounded exact reconstruction at strict-NAND complexity C(f)<=d.

Here d>=1 is the number of essential inputs. Constants are outside this
contract. Complete negative search is distinct from a resource refusal.
The ordinary normalization proof is in SPARSE_NAND_RECONSTRUCTION.md.
"""
from __future__ import annotations
from dataclasses import dataclass
import argparse
import hashlib
import json
import time
from pathlib import Path
from continuation import read_once_nand as ro
from continuation import repeated_z_nand as rz

@dataclass(frozen=True)
class Limits:
    max_n: int = 4
    max_partitions: int = 15
    max_table_lookups: int = 100_000
    max_recognizer_calls: int = 64
    seconds: float = 20.0

class _Refusal(Exception):
    pass

class _Budget:
    def __init__(self, limits):
        self.limits=limits
        self.deadline=time.monotonic()+limits.seconds
        self.counts={'partitions':0,'table_lookups':0,'recognizer_calls':0}
    def check(self):
        if time.monotonic() >= self.deadline:
            raise _Refusal('time_limit')
    def charge(self, name):
        self.check()
        maximum=getattr(self.limits,'max_'+name)
        if self.counts[name] >= maximum:
            raise _Refusal(name+'_limit')
        self.counts[name]+=1
    def bit(self,mask,row):
        self.charge('table_lookups')
        return (mask>>row)&1


def verify_witness(n,mask,witness,max_gates):
    """Independent actual DAG evaluation, without decomposition identities."""
    if type(n) is not int or not 1<=n<=4 or type(mask) is not int or mask<0 or mask.bit_length()>(1<<n):
        return False
    if type(max_gates) is not int or not 0<=max_gates<=n:
        return False
    if type(witness) is not dict or set(witness)!={'gates','output'}:
        return False
    gates,output=witness['gates'],witness['output']
    if type(gates) is not list or len(gates)>max_gates or type(output) is not int or not 0<=output<n+len(gates):
        return False
    for i,pair in enumerate(gates):
        if type(pair) is not list or len(pair)!=2 or any(type(v) is not int or not 0<=v<n+i for v in pair):
            return False
    actual=0
    for row in range(1<<n):
        values=[bool((row>>i)&1) for i in range(n)]
        for left,right in gates:
            values.append(not(values[left] and values[right]))
        actual|=int(values[output])<<row
    return actual==mask


def _assemble(n,W,Y,q_witness,outer_tree):
    """Emit q once and route BOTH z occurrences to that same computed wire."""
    w=len(W)
    gates=[]
    def q_wire(index):
        return W[index] if index<w else n+index-w
    for left,right in q_witness['gates']:
        gates.append([q_wire(left),q_wire(right)])
    shared=q_wire(q_witness['output'])
    def emit(node):
        if node[0]=='x':
            return Y[node[1]]
        if node[0]=='z':
            return shared
        left,right=emit(node[1]),emit(node[2])
        output=n+len(gates)
        gates.append([left,right])
        return output
    output=emit(outer_tree)
    return {'gates':gates,'output':output}


def reconstruct(n,mask,*,limits=Limits()):
    """RECONSTRUCTED / NO_SMALL_CIRCUIT / CONSTANT_OUT_OF_SCOPE /
    RESOURCE_LIMIT / MALFORMED / INTERNAL_ERROR.

    On nonconstant tables, complete negative search means C(f)>d; success
    supplies an independently simulated <=d-gate actual DAG certificate.
    max_n limits ambient inputs; no claim is made beyond these explicit caps.
    """
    counts={'partitions':0,'table_lookups':0,'recognizer_calls':0}
    def result(status,reason,**extra):
        return {'status':status,'reason':reason,'counters':dict(counts),**extra}
    if type(limits) is not Limits:
        return result('MALFORMED','invalid_limits_type')
    defaults=Limits()
    for field in ('max_n','max_partitions','max_table_lookups','max_recognizer_calls'):
        value=getattr(limits,field)
        if type(value) is not int or not 0<=value<=getattr(defaults,field):
            return result('MALFORMED','invalid_or_increased_limits')
    if type(limits.seconds) not in (int,float) or not 0<=limits.seconds<=defaults.seconds:
        return result('MALFORMED','invalid_seconds')
    if type(n) is not int or n<1 or type(mask) is not int or mask<0:
        return result('MALFORMED','invalid_n_or_mask')
    if n>limits.max_n:
        return result('RESOURCE_LIMIT','input_variable_limit')
    if mask.bit_length()>(1<<n):
        return result('MALFORMED','mask_out_of_range')
    budget=_Budget(limits)
    counts=budget.counts
    try:
        essential=[]
        for i in range(n):
            if any(budget.bit(mask,row)!=budget.bit(mask,row|(1<<i))
                   for row in range(1<<n) if not ((row>>i)&1)):
                essential.append(i)
        d=len(essential)
        if d==0:
            return result('CONSTANT_OUT_OF_SCOPE','contract_requires_nonconstant',essential_inputs=[])
        budget.charge('recognizer_calls')
        first=ro.recognize(n,mask)
        budget.check()
        if first['status']=='READ_ONCE':
            witness=first['witness']
            if not verify_witness(n,mask,witness,d-1):
                return result('INTERNAL_ERROR','read_once_certificate_failed')
            return result('RECONSTRUCTED','read_once',essential_inputs=essential,
                          gate_count=len(witness['gates']),witness=witness)
        if first['status']=='RESOURCE_LIMIT':
            raise _Refusal('read_once_dependency_limit')
        if first['status']!='NOT_READ_ONCE':
            return result('INTERNAL_ERROR','unexpected_read_once_status')
        for subset in range(1,1<<d):
            budget.charge('partitions')
            W=tuple(v for i,v in enumerate(essential) if (subset>>i)&1)
            Y=tuple(v for i,v in enumerate(essential) if not ((subset>>i)&1))
            rows=[]
            patterns=set()
            w_embeddings=[sum(((a>>j)&1)<<i for j,i in enumerate(W)) for a in range(1<<len(W))]
            y_embeddings=[sum(((a>>j)&1)<<i for j,i in enumerate(Y)) for a in range(1<<len(Y))]
            for wrow in w_embeddings:
                row=sum(budget.bit(mask,wrow|yrow)<<a for a,yrow in enumerate(y_embeddings))
                rows.append(row)
                patterns.add(row)
                if len(patterns)>2:
                    break
            if len(patterns)!=2 or len(rows)!=len(w_embeddings):
                continue
            pattern0,pattern1=sorted(patterns)
            for orientation in (0,1):
                budget.check()
                row0,row1=(pattern0,pattern1) if orientation==0 else (pattern1,pattern0)
                q_mask=sum(int(row==row1)<<a for a,row in enumerate(rows))
                budget.charge('recognizer_calls')
                q_result=ro.recognize(len(W),q_mask)
                budget.check()
                if q_result['status']=='RESOURCE_LIMIT':
                    raise _Refusal('inner_read_once_dependency_limit')
                if q_result['status']=='NOT_READ_ONCE':
                    continue
                if q_result['status']!='READ_ONCE':
                    return result('INTERNAL_ERROR','unexpected_inner_read_once_status')
                q_witness=q_result['witness']
                if len(q_witness['gates'])!=len(W)-1 or not verify_witness(len(W),q_mask,q_witness,len(W)-1):
                    return result('INTERNAL_ERROR','inner_read_once_certificate_failed')
                outer_mask=row0|(row1<<(1<<len(Y)))
                budget.charge('recognizer_calls')
                remaining=budget.deadline-time.monotonic()
                if remaining<=0:
                    raise _Refusal('time_limit')
                outer=rz.reconstruct(outer_mask,len(Y),z_reads=2,
                                     limits=rz.Limits(seconds=min(10.0,remaining)))
                budget.check()
                if outer['status']=='RESOURCE_LIMIT':
                    raise _Refusal('repeated_z_dependency_limit')
                if outer['status']=='NOT_REPRESENTABLE':
                    continue
                if outer['status']!='REPRESENTABLE':
                    return result('INTERNAL_ERROR','unexpected_repeated_z_status')
                tree=outer['tree']
                if not rz.verify_tree(tree,outer_mask,len(Y),2):
                    return result('INTERNAL_ERROR','outer_tree_certificate_failed')
                witness=_assemble(n,W,Y,q_witness,tree)
                if len(witness['gates'])!=d or not verify_witness(n,mask,witness,d):
                    return result('INTERNAL_ERROR','assembled_certificate_failed')
                return result('RECONSTRUCTED','single_shared_subtree',essential_inputs=essential,
                              gate_count=len(witness['gates']),witness=witness,
                              decomposition={'w_inputs':list(W),'y_inputs':list(Y),
                                             'q_mask':q_mask,'outer_mask':outer_mask,
                                             'orientation':orientation})
        return result('NO_SMALL_CIRCUIT','all_partitions_and_orientations_exhausted',
                      essential_inputs=essential,gate_budget=d)
    except _Refusal as error:
        return result('RESOURCE_LIMIT',str(error))
    except (KeyError,IndexError,TypeError,ValueError):
        return result('INTERNAL_ERROR','dependency_or_certificate_schema_error')


def _row_mask(n,function):
    return sum(int(bool(function([(row>>i)&1 for i in range(n)])))<<row for row in range(1<<n))

def source_sha256_lf():
    data=Path(__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
    return hashlib.sha256(data).hexdigest()

def report_digest(report):
    body={k:v for k,v in report.items() if k!='report_sha256'}
    return hashlib.sha256((json.dumps(body,sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\n').encode()).hexdigest()

def build_demo():
    def reused(x):
        z,a,b,c=x
        return not ((not(z and a)) and (not((not(z and b)) and c)))
    def internal(x):
        a,b,c,d=x
        q=not(a and b)
        return not ((not(q and c)) and (not(q and d)))
    examples=[('positive_projection',1,2),('negative_projection',1,1),('and2_empty_outer_group',2,8),
              ('nand3',3,127),('reused_primary',4,_row_mask(4,reused)),
              ('shared_internal',4,_row_mask(4,internal)),('parity4',4,_row_mask(4,lambda x:sum(x)%2)),
              ('constant_one_excluded',2,15)]
    report={'format':'sparse-nand-reconstruction-demo-v1',
            'scope':'Nonconstant strictNAND C(f)<=d boundary, ordinary proof and bounded checks; not Lean-formalized/novelty/PvsNP.',
            'mask_encoding':'bit assignment; assignment=sum_i x_i*2^i',
            'source_sha256_lf':source_sha256_lf(),
            'source_hash_normalization':'CRLF->LF then CR->LF; other bytes unchanged',
            'report_hash_encoding':'compact sorted-key ASCII JSON excluding report_sha256, one terminal LF',
            'limits':vars(Limits()),
            'examples':[{'name':name,'n':n,'mask':mask,'result':reconstruct(n,mask)} for name,n,mask in examples]}
    report['report_sha256']=report_digest(report)
    return report

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args(argv)
    report=build_demo()
    if args.write:
        path=Path(__file__).resolve().parent/'results'/'sparse-nand-reconstruction-demo.json'
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'source_sha256_lf':report['source_sha256_lf'],'report_sha256':report['report_sha256'],
                      'statuses':{row['name']:row['result']['status'] for row in report['examples']}},sort_keys=True))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
