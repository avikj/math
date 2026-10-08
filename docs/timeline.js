(function(){
var entries=window.TIMELINE_ENTRIES||[];
function esc(s){return String(s||"").replace(/[&<>"]/g,function(c){return {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c];});}
function uses(xs){return (xs||[]).map(function(x){return '<a href="#'+esc(x[1])+'">'+esc(x[0])+'</a>';}).join(', ');}
var finalEntry={d:"this page",t:"The identities close",s:"0 1 2 3 4 5 6 7 8 9",current:true,
 b:"The imported interfaces are composed rather than placed beside one another.",
 m:"A ≃ B → A ≡ B → transport\nreversible operation = transport\nloss = forgotten fibre information\nanswer = normal form",
 n:"Then the same exact maps continue: ℕ = finite sets / ≅; gcd/lcm = meet/join on prime-exponent vectors; σ² = −1; F = E+iB turns the two vacuum evolution equations into i∂ₜF = ∇×F; solutions = F⁻¹(true); decision = truncation of that fibre; |sort⁻¹(s)| = n!; ∏ merges C(a+b,a) = n!; and inversion count is exact distance for inversion-removing adjacent swaps.",
 u:[["0.8","s0.8"],["1.2","s1.2"],["3.2","s3.2"],["4.2","s4.2"],["5.13","s5.13"],["6.5","s6.5"],["7.4","s7.4"],["8.6","s8.6"],["9.8","s9.8"],["9.13","s9.13"]]};
entries=entries.concat([finalEntry]);
var button=document.createElement("button");button.id="timeline-toggle";button.type="button";button.textContent="timeline";button.setAttribute("aria-expanded","false");button.setAttribute("aria-controls","timeline");
var aside=document.createElement("aside");aside.id="timeline";aside.setAttribute("aria-label","Technical lineage");aside.setAttribute("aria-hidden","true");
aside.innerHTML='<button id="timeline-close" type="button" aria-label="Close timeline">×</button><div class="tl-head"><h2>Technical lineage</h2><p>Only prior formalizations used by the argument. The mathematics is on the page; this records where the modern literature made each required interface explicit.</p></div><div class="tl"></div>';
var root=aside.querySelector(".tl");
entries.forEach(function(e){
 var sec=document.createElement("section");sec.className="tl-entry"+(e.current?" current":"");sec.dataset.sections=e.s||"";
 sec.innerHTML='<div class="tl-date">'+esc(e.d)+'</div><h3>'+esc(e.t)+'</h3><p>'+esc(e.b)+'</p>'+(e.m?'<div class="tl-math">'+esc(e.m)+'</div>':'')+(e.n?'<p class="tl-note">'+esc(e.n)+'</p>':'')+(e.u?'<p class="tl-use">On this page: '+uses(e.u)+'.</p>':'');
 root.appendChild(sec);
});
document.body.appendChild(button);document.body.appendChild(aside);
function set(open){aside.classList.toggle("open",open);aside.setAttribute("aria-hidden",String(!open));button.setAttribute("aria-expanded",String(open));}
button.onclick=function(){set(!aside.classList.contains("open"));};aside.querySelector("#timeline-close").onclick=function(){set(false);};
document.addEventListener("keydown",function(e){if(e.key==="Escape")set(false);});
aside.addEventListener("click",function(e){if(e.target.closest("a"))set(false);});
function activeSection(){
 var nodes=Array.prototype.slice.call(document.querySelectorAll("main h2"));
 var y=window.scrollY+window.innerHeight*.28, cur="0";
 nodes.forEach(function(h){if(h.offsetTop<=y){var n=h.querySelector(".n");if(n)cur=n.textContent.replace(".","");}});
 return cur;
}
var last="";
function sync(){
 var cur=activeSection();if(cur===last)return;last=cur;
 var candidates=Array.prototype.slice.call(root.querySelectorAll(".tl-entry")).filter(function(e){return (" "+e.dataset.sections+" ").indexOf(" "+cur+" ")>=0;});
 root.querySelectorAll(".tl-entry.focus").forEach(function(e){e.classList.remove("focus");});
 candidates.forEach(function(e){e.classList.add("focus");});
 if(aside.classList.contains("open")&&candidates.length)candidates[candidates.length-1].scrollIntoView({block:"center",behavior:"smooth"});
}
window.addEventListener("scroll",sync,{passive:true});sync();
})();