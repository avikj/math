#!/usr/bin/env node
// Transport, job validation, source generation, and independent result checking.
// NO mining/search loop lives in this file. Candidates remain native SUP data.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';

export const HERE = path.dirname(fileURLToPath(import.meta.url));
export const ROOT = path.resolve(HERE, '../../..');
export const GENESIS = '01000000' + '00'.repeat(32) +
  '3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a' +
  '29ab5f49ffff001d1dac2b7c';
export const GENESIS_HASH = '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f';
const MAX256 = (1n << 256n) - 1n;
const LIMITS = {
  mainnet: BigInt('0x00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff'),
  regtest: (1n << 255n) - 1n,
};
const K = ('428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5 ' +
  'd807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174 ' +
  'e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da ' +
  '983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967 ' +
  '27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85 ' +
  'a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070 ' +
  '19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3 ' +
  '748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2').split(' ');
const IV = '6a09e667 bb67ae85 3c6ef372 a54ff53a 510e527f 9b05688c 1f83d9ab 5be0cd19'.split(' ');
export function requireThat(ok, message) { if (!ok) throw new Error(message); }
export function hex(s, bytes, field) {
  requireThat(typeof s === 'string' && new RegExp(`^[0-9a-fA-F]{${bytes * 2}}$`).test(s), `${field}: expected ${bytes} bytes of plain hex`);
  return s.toLowerCase();
}
export function sha256(bytes) { return crypto.createHash('sha256').update(bytes).digest(); }
export function hashHeader(header) { return Buffer.from(sha256(sha256(Buffer.from(header, 'hex')))).reverse().toString('hex'); }
export function compact(bits) {
  const n = Number.parseInt(hex(bits, 4, 'nBits'), 16);
  const size = n >>> 24;
  const word = n & 0x007fffff;
  requireThat(!(n & 0x00800000), 'negative compact target');
  requireThat(!(size > 34 || (word > 0xff && size > 33) || (word > 0xffff && size > 32)), 'overflowed compact target');
  const target = size <= 3 ? BigInt(word) >> BigInt(8 * (3 - size)) : BigInt(word) << BigInt(8 * (size - 3));
  requireThat(target > 0n && target <= MAX256, 'zero or out-of-range target');
  return target;
}
export function bitsOf(buffer) {
  return [...buffer].flatMap(b => Array.from({ length: 8 }, (_, i) => (b >>> (7 - i)) & 1));
}
function bendBits(bits) { return '[' + bits.map(b => b ? 'True' : 'False').join(', ') + ']'; }
function hvmBits(bits) { return bits.reduceRight((t, b) => `#Con{${b},${t}}`, '#Nil'); }
function wordBits(s) { return Array.from({ length: 32 }, (_, i) => Number((BigInt('0x' + s) >> BigInt(i)) & 1n)); }
function padBytes(length) {
  const zeroes = (56 - ((length + 1) % 64) + 64) % 64;
  const p = Buffer.alloc(1 + zeroes + 8); p[0] = 0x80;
  p.writeBigUInt64BE(BigInt(length) * 8n, p.length - 8); return p;
}
function constant(name, buffer) { return `def ${name}() -> Bool[]:\n  ${bendBits(bitsOf(buffer))}\n`; }
export function constantsSource() {
  return '# Literal FIPS constants; no candidate is evaluated by this generator.\n' +
    'def btcK() -> Bool[][]:\n  [' + K.map(w => bendBits(wordBits(w))).join(',\n    ') + ']\n' +
    'def btcIV() -> Bool[][]:\n  [' + IV.map(w => bendBits(wordBits(w))).join(',\n    ') + ']\n' +
    `def btcZeroW() -> Bool[]:\n  ${bendBits(Array(32).fill(0))}\n` +
    constant('btcPad80', padBytes(80)) + constant('btcPad32', padBytes(32));
}
export function validateJob(input) {
  requireThat(input && input.format === 'bitcoin-native-job-v1', 'unsupported job format');
  const allowed = new Set(['format','job_id','network','headers','nonce','max_solutions','share_target','provenance']);
  requireThat(Object.keys(input).every(k => allowed.has(k)), 'unknown job field (round count, arbitrary target, and hash overrides are forbidden)');
  requireThat(typeof input.job_id === 'string' && /^[\w.-]{1,128}$/.test(input.job_id), 'invalid job_id');
  requireThat(Object.hasOwn(LIMITS, input.network), 'network must be mainnet or regtest; no guessed consensus parameters');
  requireThat(Array.isArray(input.headers) && input.headers.length > 0 && input.headers.length <= 256, 'supply 1..256 serialized 80-byte header templates');
  const headers = input.headers.map((h, i) => hex(h, 80, `headers[${i}]`));
  const prefixes = headers.map(h => h.slice(0, 152));
  requireThat(new Set(prefixes).size === prefixes.length, 'duplicate 76-byte templates: retain distinct provenance outside, do not silently deduplicate it');
  const nBits = Buffer.from(headers[0], 'hex').readUInt32LE(72).toString(16).padStart(8,'0');
  const target = compact(nBits);
  requireThat(target <= LIMITS[input.network], 'target exceeds network powLimit');
  const parent = headers[0].slice(8,72);
  for (const h of headers) {
    requireThat(h.slice(8,72) === parent, 'one run must concern one previous block');
    requireThat(Buffer.from(h,'hex').readUInt32LE(72).toString(16).padStart(8,'0') === nBits, 'all templates must use the same nBits');
  }
  requireThat(input.nonce && Object.keys(input.nonce).every(k => ['base','mask'].includes(k)), 'nonce requires only base and mask');
  const base = hex(input.nonce.base,4,'nonce.base'), mask = hex(input.nonce.mask,4,'nonce.mask');
  const b = BigInt('0x'+base), m = BigInt('0x'+mask);
  requireThat((b & m) === 0n, 'nonce.base must be zero in every free/masked bit');
  const free = [...m.toString(2)].filter(c => c === '1').length;
  const count = BigInt(headers.length) * (1n << BigInt(free));
  const limit = input.max_solutions ?? 1;
  requireThat(Number.isInteger(limit) && limit >= 1 && limit <= 100, 'max_solutions must be 1..100');
  const share = input.share_target === undefined ? null : BigInt('0x'+hex(input.share_target,32,'share_target'));
  requireThat(share === null || (share >= target && share <= MAX256), 'share_target must be at least the network target and fit 256 bits');
  return {
    ...input, headers, nonce: {base,mask}, max_solutions:limit,
    nBits, block_target: target.toString(16).padStart(64,'0'),
    search_target: (share ?? target).toString(16).padStart(64,'0'),
    output_kind: share === null ? 'block-header-pow' : 'pool-share-or-block-header-pow',
    candidate_count: count.toString(), free_nonce_bits:free,
    template_authority:'supplied by the executor; no transaction/chain-context validity is inferred',
  };
}
export function inputSource(job) {
  let label = 0;
  const balanced = values => {
    if (values.length === 1) return values[0];
    // HVM4 encodes a label name in 24 bits: four base64 characters at most.
    const k = Math.floor(values.length/2), name = `T${label++}`;
    return `&${name}{${balanced(values.slice(0,k))},${balanced(values.slice(k))}}`;
  };
  const prefixDefs = job.headers.map((h,i) => `@btcTemplate${i} = ${hvmBits(bitsOf(Buffer.from(h.slice(0,152),'hex')))}`);
  const base = BigInt('0x'+job.nonce.base), mask = BigInt('0x'+job.nonce.mask);
  const nonceBits = [];
  for (let byte = 0; byte < 4; ++byte) for (let bit = 7; bit >= 0; --bit) {
    const i = byte*8+bit, flag = 1n << BigInt(i);
    nonceBits.push(mask & flag ? `&N${i}{0,1}` : String(Number((base >> BigInt(i)) & 1n)));
  }
  return '// Actual Bitcoin candidate family, held as one SUP value.\n' +
    prefixDefs.join('\n') + '\n' +
    `@btcPrefixes = ${balanced(job.headers.map((_,i) => '@btcTemplate'+i))}\n` +
    `@btcNonces = ${hvmBits(nonceBits)}\n` +
    '@btcCandidates = @DbtcAppend(@btcPrefixes, @btcNonces)\n' +
    `@btcTarget = ${hvmBits(bitsOf(Buffer.from(job.search_target,'hex')))}\n` +
    '// Existing SupGen keep/filter pattern: no host enumeration; failure is ERA.\n' +
    '@btcKeep = λ{#Pair: λbtcVerdict. λbtcReceipt. (λ{0: λbtcNo. &{}; _: λbtcYes. λ{#Pair: λbtcHeader. λbtcProof. #Hit{btcHeader, btcProof}}})(btcVerdict)(btcReceipt)}\n' +
    '@main = @btcKeep(@DbtcRun(@btcTarget, @btcCandidates))\n';
}
export function gateSource() {
  const empty = Buffer.from(''), abc = Buffer.from('abc');
  const target = compact('1d00ffff').toString(16).padStart(64,'0');
  return 'import MiningClaim\n' +
    constant('btcGateEmpty', Buffer.concat([empty,padBytes(0)])) +
    constant('btcGateABC', Buffer.concat([abc,padBytes(3)])) +
    constant('btcGateE', Buffer.from('e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855','hex')) +
    constant('btcGateA', Buffer.from('ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad','hex')) +
    constant('btcGateHeader',Buffer.from(GENESIS,'hex')) +
    constant('btcGateDigest',Buffer.from(GENESIS_HASH,'hex').reverse()) +
    constant('btcGateTarget',Buffer.from(target,'hex')) +
    'def main() -> Bool[]:\n  [btcEqBits(btcFlatten(btcBlocks(1n, btcIV(), btcGateEmpty())), btcGateE()),\n' +
    '   btcEqBits(btcFlatten(btcBlocks(1n, btcIV(), btcGateABC())), btcGateA()),\n' +
    '   btcEqBits(btcDouble80(btcGateHeader()), btcGateDigest()),\n' +
    '   btcAccept(btcGateTarget(), btcGateHeader()),\n' +
    '   btcNot(btcAccept(btcGateTarget(), [])),\n' +
    '   btcEqBits(btcRestore(btcGateTarget(), btcGateHeader()), btcGateHeader())]\n';
}
function dump(file,obj) { fs.writeFileSync(file,JSON.stringify(obj,null,2)+'\n'); }
function fileDigest(file) { return sha256(fs.readFileSync(file)).toString('hex'); }
function sourceRoot(out) { return path.join(out,'source'); }
export function prepare(jobFile,out) {
  requireThat(fs.statSync(jobFile).size <= 2_000_000, 'job file too large');
  const job = validateJob(JSON.parse(fs.readFileSync(jobFile,'utf8')));
  requireThat(!fs.existsSync(out) || fs.readdirSync(out).length === 0, 'output directory is not empty; never overwrite an earlier run');
  fs.mkdirSync(sourceRoot(out),{recursive:true});
  const sources = {};
  for (const name of ['MiningSha256.bend','MiningClaim.bend']) {
    const p=path.join(HERE,name); fs.copyFileSync(p,path.join(sourceRoot(out),name)); sources[p]=fileDigest(p);
  }
  for (const name of ['Prelude.bend','Carrier.bend']) {
    const p=path.resolve(HERE,'../port',name); fs.copyFileSync(p,path.join(sourceRoot(out),name)); sources[p]=fileDigest(p);
  }
  const patch=path.resolve(HERE,'../cubical-paths.patch'); sources[patch]=fileDigest(patch);
  fs.writeFileSync(path.join(sourceRoot(out),'MiningConstants.bend'),constantsSource());
  fs.writeFileSync(path.join(sourceRoot(out),'Gate.bend'),gateSource());
  fs.writeFileSync(path.join(out,'input.hvm4'),inputSource(job));
  fs.copyFileSync(jobFile,path.join(out,'job.original.json'));
  dump(path.join(out,'job.lock.json'),job);
  let revision='unavailable';
  try { revision=execFileSync('git',['-C',ROOT,'rev-parse','HEAD'],{encoding:'utf8',stdio:['ignore','pipe','ignore']}).trim(); } catch {}
  for(const name of fs.readdirSync(sourceRoot(out))) sources[name]=fileDigest(path.join(sourceRoot(out),name));
  dump(path.join(out,'manifest.json'),{format:'bitcoin-native-run-v1',created_at:new Date().toISOString(),repository_revision:revision,node:process.version,source_hashes:sources,input_sha256:fileDigest(path.join(out,'input.hvm4')),job_sha256:fileDigest(jobFile),native_execution:'not-started'});
  console.log(`Prepared ${job.candidate_count} candidates as ${fs.statSync(path.join(out,'input.hvm4')).size} bytes of native input, not enumerated headers.`);
}
export function link(compiled,input) {
  requireThat(compiled.includes('FULL RUNTIME') && /^@coe\s*=/m.test(compiled) && /^@DbtcRun\s*=/m.test(compiled), 'not the cubical full-runtime emitter output or missing btcRun');
  requireThat((compiled.match(/^@main\s*=/gm)||[]).length===1, 'expected exactly one library main');
  return compiled.replace(/^@main\s*=/m,'@btcLibraryMain =')+'\n'+input;
}
function stripAnsi(s) { return s.replace(/\x1b\[[0-9;]*m/g,''); }
class Reader {
  constructor(s) { this.s=s; this.p=0; }
  ws() { while (/\s/.test(this.s[this.p]??'') && this.p<this.s.length) ++this.p; }
  take(t) { this.ws(); requireThat(this.s.startsWith(t,this.p),`unexpected native output at byte ${this.p}: expected ${t}`); this.p+=t.length; }
  bits() {
    const bits=[]; let n=0;
    for (;;) {
      this.ws();
      if (this.s.startsWith('#Nil',this.p)) { this.p+=4; if (this.s.startsWith('{}',this.p)) this.p+=2; break; }
      this.take('#Con'); this.take('{'); this.ws();
      const b=this.s[this.p++]; requireThat(b==='0'||b==='1','non-Boolean or unresolved bit in native output');
      bits.push(Number(b)); this.take(','); ++n;
      requireThat(n<=640,'native bit list exceeds header width');
    }
    while(n--) this.take('}'); return bits;
  }
}
function fromBits(bits) {
  requireThat(bits.length%8===0,'bit vector is not byte-aligned');
  return Buffer.from(Array.from({length:bits.length/8},(_,i)=>bits.slice(i*8,i*8+8).reduce((a,b)=>a*2+b,0)));
}
export function validateHeader(job,header) {
  hex(header,80,'emitted header');
  const template=job.headers.findIndex(h=>h.slice(0,152)===header.slice(0,152));
  requireThat(template>=0,'emitted header changes immutable job fields');
  const nonce=BigInt(Buffer.from(header,'hex').readUInt32LE(76));
  requireThat((nonce & (0xffffffffn ^ BigInt('0x'+job.nonce.mask)))===BigInt('0x'+job.nonce.base),'emitted nonce outside the declared family');
  const digest=hashHeader(header), numeric=BigInt('0x'+digest);
  requireThat(numeric<=BigInt('0x'+job.search_target),'native survivor FAILS independent full SHA256d / target verification');
  return {header,hash:digest,nonce:Number(nonce),template_index:template,meets_search_target:true,meets_block_target:numeric<=BigInt('0x'+job.block_target)};
}
function readText(file) { requireThat(fs.statSync(file).size<=128*1024*1024,'output exceeds parser memory cap; raw output retained'); return stripAnsi(fs.readFileSync(file,'utf8')); }
function checkNoise(noise) {
  for(const line of noise.split('\n').map(x=>x.trim()).filter(Boolean)) {
    // `-C` annotates each collapsed result with its interaction count (`#N`, dimmed).
    requireThat((/^[-=]/.test(line) || /^#\d+$/.test(line)) && !/error|fail|stuck|invalid|usage/i.test(line),'unexpected runtime output: '+line.slice(0,160));
  }
}
export function verifyGate(text) {
  const s=stripAnsi(text), start=s.indexOf('#Con'); requireThat(start>=0,'native gate returned no Boolean list');
  const r=new Reader(s); r.p=start; const bs=r.bits();
  requireThat(bs.length===6&&bs.every(b=>b===1),'native SHA/Bitcoin/transport conformance gate failed');
  checkNoise(s.slice(0,start)+'\n'+s.slice(r.p)); return bs;
}
export function verifyResults(job,text) {
  const s=stripAnsi(text), hits=[], seen=new Set(); let cursor=0, noise='';
  for (;;) {
    const start=s.indexOf('#Hit',cursor); if(start<0) {noise+=s.slice(cursor);break;}
    noise+=s.slice(cursor,start); const r=new Reader(s);r.p=start;r.take('#Hit');r.take('{');
    const bs=r.bits();requireThat(bs.length===640,'native result is not an 80-byte header');r.take(',');
    const proofStart=r.p; let depth=1;
    while(r.p<s.length&&depth>0) { const ch=s[r.p++];if(ch==='{')++depth;else if(ch==='}')--depth; }
    requireThat(depth===0,'truncated native receipt');
    const proof=s.slice(proofStart,r.p-1).trim(); requireThat(proof.startsWith('#PLm'),'native result lost its cubical path receipt');
    const h=fromBits(bs).toString('hex');requireThat(!seen.has(h),'duplicate native survivor; correlation/multiplicity requires investigation');seen.add(h);
    hits.push({...validateHeader(job,h),runtime_receipt:proof});cursor=r.p;
  }
  checkNoise(noise); requireThat(hits.length<=job.max_solutions,'native collapse exceeded requested result limit'); return hits;
}
export function mark(out,phase,status,detail='') {
  fs.appendFileSync(path.join(out,'events.jsonl'),JSON.stringify({at:new Date().toISOString(),phase,status,detail})+'\n');
}
function cli(args) {
  const [cmd,...xs]=args;
  if(cmd==='prepare'&&xs.length===2) return prepare(path.resolve(xs[0]),path.resolve(xs[1]));
  if(cmd==='link'&&xs.length===3) return fs.writeFileSync(xs[2],link(fs.readFileSync(xs[0],'utf8'),fs.readFileSync(xs[1],'utf8')));
  if(cmd==='gate'&&xs.length===1) {verifyGate(readText(xs[0]));console.log('NATIVE_GATE_PASS');return;}
  if(cmd==='verify'&&xs.length===2) {
    const job=JSON.parse(fs.readFileSync(path.join(xs[0],'job.lock.json'),'utf8'));
    const hits=verifyResults(job,readText(xs[1]));dump(path.join(xs[0],'verified-hits.json'),{job_id:job.job_id,hits,scope:'proof-of-work and membership in supplied header family; not full block/chain validation'});
    console.log(`INDEPENDENTLY_VERIFIED_HITS=${hits.length}`);return;
  }
  if(cmd==='mark'&&xs.length>=3) return mark(xs[0],xs[1],xs[2],xs.slice(3).join(' '));
  if(cmd==='identity'&&xs.length===2) {
    const p=fs.realpathSync(xs[1]);console.log(JSON.stringify({role:xs[0],path:p,sha256:fileDigest(p)}));return;
  }
  throw new Error('Usage: mining.mjs prepare JOB OUT | link COMPILED INPUT OUTPUT | gate LOG | verify OUT LOG | mark OUT PHASE STATUS [DETAIL] | identity ROLE FILE');
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {cli(process.argv.slice(2));}catch(e){console.error('ERROR: '+e.message);process.exitCode=1;}
}
