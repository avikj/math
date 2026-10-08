# Ceptr: Origins, Motivations, History and Philosophical Vision (MetaCurrency Project → Ceptr, c. 2008–2017)

Environment note for the report writer: web.archive.org (Wayback Machine) is blocked by this session's egress policy ("Blocked by egress policy" on every attempt, including the plain-HTTP and CDX endpoints), the GitHub API for zippy/ceptr is not enabled for this session, forum.holochain.org does not resolve, and ceptr.decko.org / newcurrencyfrontiers.decko.org / coalitionofinvisiblecolleges.org return 403/503. Everything below therefore comes from the **live** ceptr.org, metacurrency.org, artbrock.com, P2P Foundation wiki, and third-party pages. The live ceptr.org blog still carries the 2014–2017 posts with their original dates, so the chronology is primary-sourced even without Wayback. Items I could only confirm through search-result summaries (not a fetched page) are marked "(search snippet only)".

---

## Key Question 1: When and why did Ceptr start, and how does it relate to the MetaCurrency Project and Brock's earlier currency-design work?

### Takeaway
Ceptr grew out of the MetaCurrency Project (publicly active by 2009, co-founded by Arthur Brock and Eric Harris-Braun) when the founders concluded that interoperable, non-monopolizable currencies required rebuilding the computing/protocol stack itself; Brock dated the Ceptr effort to "the past 5 years" in November 2015 (i.e. c. 2010), the codebase carries a 2013–2016 copyright, and the project only "came out of the closet" publicly in September 2014.

### Cited Findings

**Brock's pre-MetaCurrency background**
- Brock's 2011 self-description: "I'm a software architect at the Geek Gene in Denver, Colorado who mostly focuses on creating community-building tools," using "targeted currencies (alternative currencies, complementary currencies, local currencies, reputation currencies, community currencies, incentives, metrics and measures)" to encourage healthy participation. His listed companies include New Currency Frontiers, MetaCurrency Project, Flowplace, Local Capital Summit, Lifeblood Design, Geek Gene, Mile High Business Alliance, Targeted Currencies Network, Dream Team Technologies, The Foundation for Inventive Learning, Alpine Valley School — [P2P Foundation wiki: Arthur Brock](https://wiki.p2pfoundation.net/Arthur_Brock)
- Brock's earlier company Dream Team Technologies received the Colorado Ethics in Business Award c. 2001 — [artbrock.com/deeper](https://www.artbrock.com/deeper)
- artbrock.com describes his focus areas as "Culture-Hacking, Alt.Education, Targeted Currency Design, NextNet Technologies" — [artbrock.com/info via /deeper](https://www.artbrock.com/deeper)
- Brock's Mile High Business Alliance local-capital program is written up in Lietaer & Dunne, *Rethinking Money*, pp. 128–130 — [artbrock.com/deeper](https://www.artbrock.com/deeper)
- Brock spoke on a panel at the Future of Money and Technology Summit, San Francisco, Feb 28, 2011, and at "Re-Visioning Money Day" (Occupy Wall Street) Oct 24, 2011 — [artbrock.com/deeper](https://www.artbrock.com/deeper); a Vimeo clip "Arthur Brock & Eric Harris-Braun at OWS" exists — [vimeo.com/31164740](https://vimeo.com/31164740)
- "Summer 2012 Eric and I ran a gift-economy based social change incubator" (Emerging Leader Labs) — [artbrock.com/deeper](https://www.artbrock.com/deeper)
- Brock "co-created Emerging Leader Labs, Agile Learning Centers, and the MetaCurrency Project"; ALC had 4 centers at the time of that page — [redefineschool.com/arthur-brock](https://redefineschool.com/arthur-brock/)
- metacurrency.org still lists Agile Learning Centers ("micro-schools supporting self-directed education") as one of its four projects alongside Holochain & Holo, "Ceptr Framework" and the Currency Design Masterclass — [metacurrency.org](https://metacurrency.org/)
- Brock's GitHub profile bio describes Ceptr as "a total rewrite of our computing/currency/comms stack from the feminine reCEPTive capacity using the organizational patterns we find in nature" and calls Ceptr "Holochain's much more sophisticated grandmother project" (search snippet only) — [github.com/artbrock](https://github.com/artbrock)

**MetaCurrency Project founding and mission (2009–2011)**
- IFTF blog post dated Nov 16, 2009 announcing a FutureCast podcast (Nov 20, 2009, host Jerry Michalski): "The Metacurrency Project seeks to build platform and protocol standards that will allow multiple and interoperable currencies on the Internet. It is the brainchild of Brock (formerly of OS-Earth) and Eric Harris-Braun (of Open Money)." The project is "an attempt to create the infrastructure for managing open currency transactions without the need for banks" — [IFTF FutureCast, 16 Nov 2009](https://legacy.iftf.org/future-now/article-detail/futurecast-jerry-michalski-interviews-arthur-brock-on-alternative-currencies/)
- A 6-minute intro video "Why we need multiple open currencies," Ferananda Ibarra interviewing Brock and Harris-Braun, video by Alan Rosenblith (vimeo.com/4448209); the P2P wiki page for it was created/last edited 3 May 2009 — [P2P Foundation wiki](https://wiki.p2pfoundation.net/Arthur_Brock_and_Eric_Harris-Braun%27s_Introduction_to_The_MetaCurrency_Project)
- MetaCurrency's stated requirements (quoted from metacurrency.org c. 2009–2011): "We are building platforms and protocols necessary for an open source economy. This requires new technology capacities which need to function in a non-monopolizable manner," with four pillars: **Open Identity**, **Open Rules**, **Open Transport**, **Open Data** ("allow you to be a reliable authority of your own data") — [P2P Foundation wiki: Metacurrency Project](https://wiki.p2pfoundation.net/Metacurrency_Project)
- Harris-Braun's foundational framing: monetary exchange, eBay reputation, grades, coupons, airline miles "are all: formal information systems that allow communities to interact with flows," and the project's goal is "a new expressive capacity, a 'flow mechanics'" analogous to wave mechanics; "we change our focus from the information tokens, to the flows themselves" — [P2P Foundation wiki: Metacurrency Project (Discussion section)](https://wiki.p2pfoundation.net/Metacurrency_Project)
- Video "Art Brock on the MetaCurrency Living Systems Model" (interview by Mark Finnern, youtube.com/watch?v=YCYhIi7vMgk) describes "the underlying model of their work: Wealth a Living System Model"; P2P wiki page last edited Aug 19, 2012 — [P2P Foundation wiki](https://wiki.p2pfoundation.net/Art_Brock_on_the_MetaCurrency_Living_Systems_Model)
- Brock's definition (later): "Currency: A formal symbol system for shaping, enabling, and measuring flows." and, of Ceptr, "We are not building a currency." — [redefineschool.com/arthur-brock](https://redefineschool.com/arthur-brock/)
- The 2023 Enacting Cybernetics conversation gives the working definition "a formal symbol system that shapes behaviors through the signaling of values and preferences," notes Brock's earlier emphasis on incentives/behavior-shaping, says Harris-Braun's "thinking is grounded in grammars," that Brock's "spectrum of wealth" diagram derives from Jean-François Noubel, and that Brock and Harris-Braun "came up with a 50-year vision of the future they call Ceptr" — [Russell & Silverman, *Enacting Cybernetics* 1(1), 24 Apr 2023](https://enacting-cybernetics.org/articles/10.58695/ec.2)
- metacurrency.org today: "Developing tools and platforms for open sourcing the next economy"; blog heading "The World of Deep Wealth"; "Ceptr Framework" described as a next-generation distributed operating system — [metacurrency.org](https://metacurrency.org/)
- metacurrency.org/about: "current-sees" are symbol systems (tokens, badges, tickets, standards) that "shape, enable, and measure flows of resources and value"; "currency" and "current" share Latin *correre* ("to run"); "Deep Wealth is the heart of a thrivable future" (Brock); "You treasure what you measure, so measure what you treasure."; a Sovereign Accountable Commons "holds the code, assets, and communities emerging as we release the Ceptr network" — [metacurrency.org/about](https://metacurrency.org/about/)

**The "NextNet"/self-describing-computing agenda that became Ceptr (2011)**
- Peter Vander Auwera's report (31 Oct 2011) on a ~50-person MetaCurrency "Collabathon" on "NextNet" tools: NextNet defined as "A computing/protocol stack for operating a distributed Internet"; a five-layer ladder — Stream-scapes (communication composition), Decision making (flows, event-based), Currencies ("language for expression of value/wealth"), Holoptinets (immersive visualization of big data), OS Earth — and the aim of "nothing less than a self-describing computing"; guiding principle "Disintermediation of any action, at all possible layer"; Occupy Wall Street participants planning an OWS currency — [petervanstudios.com, 31 Oct 2011](http://petervanstudios.com/2011/10/31/metacurrency-collabathon-a-wealth-system/) (also quoted at [P2P wiki](https://wiki.p2pfoundation.net/Metacurrency_Project))
- Ceptr's own wiki describes it as "a fractal computing stack of self-described protocols built on a flow-centric paradigm" whose protocols grew out of the infrastructure needs of the MetaCurrency economy (search snippet only; site returned 403) — [ceptr.decko.org](https://ceptr.decko.org)
- Brock (Nov 26, 2014) says the Ceptr composability design was a deliberate contrast to the team's "earlier XGFL work" — [ceptr.org blog, 26 Nov 2014](https://ceptr.org/blog/2014-11-26-ceptr-design-receptive-capacity-breakthrough). A Korean Steemit reading series says XGFL = "eXtensible Game Format Language," MetaCurrency's first open-rules format used in Flowplace, abandoned because rule-set interoperability was harder than an XML-like format could handle (search snippet only; low-reliability secondary) — [steemit.steemapps.com/@hsalbert/4](https://steemit.steemapps.com/metacurrencyproject/@hsalbert/4)
- Harris-Braun is "a core developer of Ceptr and a co-founder of the MetaCurrency project," lead developer of the Flowplace at the Collective Intelligence Research Institute, co-founder of Glass Bead Software (P2P networking apps) — [P2P Foundation wiki: Eric Harris-Braun (last edited 1 Feb 2016)](https://wiki.p2pfoundation.net/Eric_Harris-Braun)

**Dating the start of Ceptr**
- Brock, 3 Nov 2015: the team had invested "the past 5 years" in Ceptr — [ceptr.org blog, 3 Nov 2015](https://ceptr.org/blog/2015-11-03-distributed-receptor-based-computing)
- Brock, 16 Sep 2014: "For the past few years" they had been building Ceptr and posting code to GitHub but "there's been no way for anyone to really understand what we're doing" — [ceptr.org blog, 16 Sep 2014](https://ceptr.org/blog/2014-09-16-hello-world)
- The ceptr GitHub README copyright reads 2013–2016, "The MetaCurrency Project (Eric Harris-Braun, Arthur Brock, et. al.)," 990 commits, GPL-3.0, C — [github.com/zippy/ceptr](https://github.com/zippy/ceptr)
- Holochain's blog (29 May 2020): "After roughly a decade of thinking, building, and watching projects like Bitcoin struggle with unintended consequences of their designs," the MetaCurrency Project decided to "concentrate on building and releasing one component" of "Ceptr, a nervous system for the globally connected world" — [blog.holochain.org, Dev Pulse 72](https://blog.holochain.org/play-with-a-mutual-credit-currency-and-join-the-modularity-discussion/)
- Prezi (MIT/KIT webinar, Apr 2, 2015): Ceptr has roots in the MetaCurrency Project because "we needed radically different infrastructure for our tools" — [prezi.com "Just a Spoonful of Ceptr"](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- artbrock.com MIT-KIT page description: Ceptr is "a low-level system for organizing computing and communications" and "Ceptr emerged from the MetaCurrency Project's efforts to build platforms" for resilient, distributed systems — [artbrock.com/deeper](https://www.artbrock.com/deeper) (the /ceptr/mit-kit page itself now just redirects to youtube.com/watch?v=3Db-8lD1lNA)

### Inferences
- The design lineage is: Flowplace/XGFL open-rules currency platform (c. 2008–2010) → recognition that interoperability needs self-describing protocols at the lowest layer ("OS Earth", 2011 collabathon) → Ceptr as the receptor/semantic-tree implementation of that idea (coding c. 2010–2013 onward, public from Sept 2014).
- "~2010" is the best-supported start date (Brock's "5 years" in Nov 2015); the 2013 copyright likely marks the start of the current C codebase, not the concept. A Holochain forum claim of "2006 for Ceptr" surfaced in a search summary but is low-reliability and could not be fetched.

### Gaps
- No primary source gives an exact founding date for either MetaCurrency (search summaries say "by 2008"; a ContactOut directory says 2008 but is unreliable) or Ceptr.
- Could not retrieve the first commit date of zippy/ceptr (GitHub API disabled for this session) nor the 2009 p2p-research mailing-list post (bot-protection wall).
- Wayback snapshots of metacurrency.org (2009–2013) could not be retrieved; the "four opens" text is cited via the P2P wiki's quotation of metacurrency.org rather than the archived page itself.

---

## Key Question 2: What exactly did ceptr.org and the Ceptr whitepaper/overview claim the platform would do? (All stated components/features)

### Takeaway
Ceptr was pitched as a complete replacement computing stack — "Building a Global Nervous System" / "The fabric of the new crypto-semantic Internet" — composed of receptors (nestable lightweight VMs), semantic trees as the universal data unit, Semtrex pattern matching, self-describing pluggable protocols, a signed repository (Compository), a P2P network (CeptrNet), intrinsic data integrity (the piece that became Holochain), scapes, and Sovereign Accountable Commons; by 2017 the live site split this into six sub-projects.

### Cited Findings

**Self-descriptions and taglines**
- Live ceptr.org overview heading: "Building a Global Nervous System"; Ceptr is a "Cooperative framework for distributed applications," a "Peer-to-Peer platform for building new Commons," and "an evolvable, fully distributed framework for coordination and sense-making on all scales"; it argues language, writing and printing reshaped society and that the Internet is limited by computing designed for centralized control — [ceptr.org](http://ceptr.org/); same text in the May 2017 Idealist nonprofit listing, which also uses "Quantum leap in large-scale collective social intelligence" — [idealist.org Ceptr (San Francisco)](https://www.idealist.org/es/ong/2dbbecaa35804e2896fe91bc411b8e32-ceptr-san-francisco)
- GitHub: "Ceptr: The fabric of the new crypto-semantic Internet"; tagline "(a recomposable medium for distributed social computing) || (semantic self-describing protocol stacks)"; it "provides a new computing stack for semantic self-describing data and protocols" — [github.com/zippy/ceptr](https://github.com/zippy/ceptr)
- MIT/KIT webinar deck: Ceptr is "distributed, decentralized, interoperable, resilient, composable, and semantic infrastructure," "Way beyond block-chain, APIs or RDF !", built in C; data always carries semantics/structure/context, "Cannot instantiate meaningless data" — [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- 2017 residency call: "At Ceptr we're building a platform for distributed applications that will power new forms of human collaboration," modeled on patterns in nature for fairer governance and wealth creation — [P2P Foundation blog repost, 9 Jun 2017](https://blog.p2pfoundation.net/summer-build-next-internet/)

**Components as enumerated in the *Ceptr Revelation* (Brock & Harris-Braun, status "Concept"; internal text says "Today, in 2015" and projects release "in early 2017")** — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation)
1. **Receptors** – nestable units of state, processing and signaling; "lightweight virtual machines" that receive signals.
2. **VMhosts** – special receptors interfacing with the host OS.
3. **Compository** – versioned, signed repository of receptors addressed by Compository IDs.
4. **CeptrNet** – P2P routing/addressing receptor using permanent UUIDs and "triangulation" for joining.
5. **Semtrex** – regular-expression-style parser/matcher for semantic trees.
6. **Scapes** – relational structures organizing data by context and variability, offered in place of RDF-style assertions (a separate scape-geometry document is referenced).
7. **Self-describing protocols** – templates with slots for connections, roles, goals, usage, plus expectation statements.
8. **Intrinsic Data Integrity** – signed transaction chains, Merkle trees, hash chains, DHT storage with redundancy.
9. **Sovereign Accountable Commons (SAC)** – collectively run, signed, peer-equal applications, compared to DAOs.
- Stated design principles: Learn from nature; Unenclosable (open and peered); Foster coherence and follow convergence; Intrinsic data integrity; Fractal sovereignty (individuals can fork a group and keep their assets); Optimized for evolution (versioning/deprecation built in); "The model is: Trust your own node." — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation)
- Vision lines: subtitle "Applying the patterns of living systems to upgrade social intelligence"; "Humanity is poised on the edge of a quantum leap in evolution"; Ceptr supplies "the building blocks" for "an explosion of new patterns of collective intelligence on every scale"; "Everything should just work together easily."; "Since a system that can be corrupted will eventually get corrupted" — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation)
- Many sections are marked "Still to write/expand"; published by The MetaCurrency Project under CC BY-SA 4.0 — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation)

**Components as presented in the Apr 2, 2015 MIT/KIT webinar deck** — [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- Receptors (membranes, fractal organization, bound carriers, lightweight VMs); Semtrex (semantic tree regular expressions); **Expectations** ("ON carrier EXPECT semtrex pattern DO action", Prolog-like); **RunTrees** (semantic stack replacing bytecode, carrying its own debug info); CeptrNet (sharded DHT, back-end sync, learns physical topology); Compository (author/reviewer signatures generating a CompositionID); **Coherence** (membranes, state, indexing); **H.O.P.E.** (Higher Order Programming Environment).

**Components as presented in Brock's Nov 2015 "Distributed Receptor-Based Computing" brief (for Rebooting the Web of Trust, SF, Nov 3–4, 2015)** — [ceptr.org blog, 3 Nov 2015](https://ceptr.org/blog/2015-11-03-distributed-receptor-based-computing)
- Receptors as lightweight VMs; signed chains with configurable Byzantine fault tolerance; semantic memory/stacks and a semantic-tree regex engine; pluggable protocols where a receptor can install the capacity to read a message it couldn't previously parse ("Ceptr protocols are not textual descriptions for human protocol developers"); shared code/vocabulary repository; network-wide persistent listeners; permanent UUID identity with public keys in a sharded DHT ("not temporary, reassigned, or segmented for routing"); capability tokens, signed messages, smart contracts; reputation-based thresholds; "progressive trust" (anonymous → vouched). Stated goals: semantics "into the lowest levels of storage and computation," blockchain-like decentralized storage/computation, rapid code evolution and deprecation, "fractal coherence." He notes that web-of-trust, blockchain, semantic-web, federated-identity and mesh projects each tackle one slice and that conventional tools are "cobbled together."

**Semantic trees / Semantic Alternation (2014–2016 blog posts)**
- "Receptors are lightweight virtual machines built from semantic trees" with browser visualizations (Apr 6, 2015, Harris-Braun) — [ceptr.org blog](https://ceptr.org/blog/2015-04-06-semantic-trees); Semtrex introduced as the pattern-matching tool for semantic trees (Jun 2, 2016) — [ceptr.org blog](https://ceptr.org/blog/2016-06-02-musing-on-coding-in-ceptr-making-sense-of-data); signaling via aspects, conversations and expectations (Apr 27, 2016) — [ceptr.org blog](https://ceptr.org/blog/2016-04-27-musings-on-coding-in-ceptr-signaling)
- "Semantic Alternation": an object's meaning shifts with context (Nov 29, 2014) — [ceptr.org blog](https://ceptr.org/blog/2014-11-29-building-meaning-through-semantic-alternation)

**Sub-projects on the live (Jan 2017 onward) ceptr.org** — [ceptr.org](http://ceptr.org/)
- Pluggable Protocols / Pcubed (/projects/pcubed): self-describing protocols + universal parser; Holochain (/projects/holochain): data integrity engine for P2P apps; Holo (/projects/holo): distributed app hosting; Sovereign Commons (/projects/sovereign): organizations encoded in app code; Neural Internetworking (/projects/neural): "sticky" requests that fire when conditions are met; Ceptr Core (/projects/core): integrating framework with VM hosts and fractal receptors. Back-end "mostly Go," front-end JavaScript; Mattermost and Gitter channels; content CC BY-SA 4.0.
- Harris-Braun, Jan 17, 2017: the team "broken the Ceptr development effort into some smaller sub-projects that are each independently valuable": Holochain (distributed data store, prototype finished in a recent sprint, moved to Go), Pcubed (extracting semantic trees + semtrex from the C code), ceptr-core (Holochain + Pcubed + VM Host = "fractal receptor compute fabric"); remaining C expected to convert to Go — [ceptr.org blog, 17 Jan 2017](https://ceptr.org/blog/2017-01-17-restructuring-ceptr-sub-projects)

**Full whitepaper index on ceptr.org (status labels as shown; none dated on-page)** — [ceptr.org/whitepapers](https://ceptr.org/whitepapers/)
1. Holo Cryptocurrency: Infrastructure for Global Scale and Stable Value (Draft) – /whitepapers/holo
2. Holo: Green Paper (Released)
3. Plugable Protocol for Protocols: Pcubed – "Fundamental Interoperability through Self-Describing Protocols" (Concept), authors Brock & Harris-Braun – [/whitepapers/protocols](https://ceptr.org/whitepapers/protocols)
4. Sovereign Accountable Commons: Surpassing Smart Contracts for Social Coherence (Concept) – /whitepapers/sac
5. Fallacy of Individualism: Hacking Social Compulsion for Commonwealth (Concept) – /whitepapers/fallacy
6. Grammatic Capacities and the Evolution of Complex Adaptive Systems (Pre-release Draft) – /whitepapers/grammatics
7. A Fractal Virtual Machine System Framework as New Networked Global Nervous System (Concept), authors Brock & Harris-Braun – [/whitepapers/fractalvm](https://ceptr.org/whitepapers/fractalvm)
8. Network Intelligence: From Shared Network Storage to Distributed Associative Memory (Concept) – /whitepapers/netintel
9. Holoptinets: Large-Scale Self-Reflective Functional Intelligence (Concept) – /whitepapers/holoptinets
10. Holochain: Scalable, agent-centric, distributed computing (Alpha 0 Draft) – /whitepapers/holochain
11. Mutual Credit Cryptocurrencies: Beyond Blockchain Bottlenecks (Published) – /whitepapers/mutual-credit
12. Ceptr Revelation (Concept) – /whitepapers/revelation
- Note: the live /whitepapers/protocols and /whitepapers/fractalvm pages contain only title/author/status stubs, no body text.

### Inferences
- The 2017 sub-project list is the Revelation's component list re-packaged: Intrinsic Data Integrity → Holochain; self-describing protocols + Semtrex → Pcubed; SAC → Sovereign Commons; network-wide listeners/associative memory → Neural Internetworking; receptors/VMhosts → Ceptr Core. "Holoptinets" survives from the 2011 five-layer ladder.
- No document titled "Ceptr: Building the Next Internet" was found; the closest phrasing is the June 2017 residency call "This Summer, Build the Next Internet!" and the 2016 blog's "next economy and next Internet toolset."

### Gaps
- Pre-2017 versions of ceptr.org (overview/projects/people pages, 2013–2016) could not be retrieved (Wayback blocked); the Jan 2017 restructuring post implies the earlier site presented Ceptr as a single monolithic project.
- The bodies of the Pcubed, fractalvm, netintel, holoptinets, grammatics and SAC whitepapers were not retrievable (stub pages or 403), so their specific claims are not captured.

---

## Key Question 3: What is the biological metaphor (receptors, signals, membranes, cells, organisms) and how did Brock explain it?

### Takeaway
Brock frames Ceptr around *receptive capacity* — the idea (from cochlear hairs, retinas, RNA, atomic valences) that a system should first be able to receive a general carrier and then install the capacity to interpret new symbols, rather than failing on anything unknown; receptors with membranes nest fractally like cells in organisms, protocols are carrier/signal patterns common to physics, cells, speech and TCP/IP, and the whole is meant to be a "global nervous system" with immune-like filtering and "no CEO cell."

### Cited Findings
- Name: the Revelation says the platform's name derives from the Latin root of "receptor" (search snippet only) — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation); the MIT/KIT deck says Ceptr gets its name from being built out of receptors (search snippet only) — [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- Brock, "Ceptr Design: Receptive Capacity Breakthrough" (26 Nov 2014, excerpted from the Revelation): the breakthrough was realizing systems should first receive a general carrier (sound, light) before interpreting specific symbols — "receptive capacity comes before the symbols"; Ceptr "is designed to define and receive semantics, protocols, and carriers" and when it meets an unknown symbol/protocol can install the capacity to understand it; analogies: cochlear hairs respond to frequencies not words, eyes to light not objects, RNA holds the pattern from which DNA is built, atomic valences are receptive slots for electrons, surfaces are receptive to walking/sitting; he links this to "the subtle power of yin" vs the solidity of yang — [ceptr.org blog, 26 Nov 2014](https://ceptr.org/blog/2014-11-26-ceptr-design-receptive-capacity-breakthrough)
- Same post on language: phonemes → word parts → words → phrases → sentences → narratives, but layering is not purely bottom-up — listeners tolerate accents and errors because each layer does some independent sense-making; "If every layer depended strictly on base units, one error would corrupt everything above it," which is why most computer interfaces "break easily" — [ceptr.org blog, 26 Nov 2014](https://ceptr.org/blog/2014-11-26-ceptr-design-receptive-capacity-breakthrough)
- Revelation metaphors: receptors compared to senses and to RNA; the **carrier/signal/protocol** pattern recurs "in physics, cells, speech, and TCP/IP"; Accountable Commons define "membranes to membership"; "each cell carries the instructions for cooperation, with no 'CEO cell'"; immune system = filtering unhealthy participants and reputation erosion; mirror neurons = distributed receptor instances; protein folding = relationships folding into higher-order **scapes**; "strange loop": each node is a genotype (VMhost) that exists at a phenotype address in the network; "Ceptr is structured the same as these patterns of collective intelligence found in nature." — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation)
- Brock, "I am a Strange Loop… Wouldn't Ceptr likely be Strange Loop Too?" (14 Nov 2014) applies Hofstadter's self-reference to Ceptr — [ceptr.org blog](https://ceptr.org/blog/2014-11-14-i-am-a-strange-loop-ceptr-too)
- Harris-Braun, "Ceptr and the Bicameral Brain" (9 Jul 2016) contrasts linear vs. pattern-matching modes of programming — [ceptr.org blog](https://ceptr.org/blog/2016-07-09-ceptr-and-the-bicameral-brain)
- Webinar deck: receptors "have membranes, are organized fractally, receive and send signals over bound carriers" — [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- Overview page: Ceptr is "modeled on natural systems"; heading "Building a Global Nervous System"; whitepaper 7's title calls it a "New Networked Global Nervous System" — [ceptr.org](http://ceptr.org/), [ceptr.org/whitepapers](https://ceptr.org/whitepapers/)
- Brock's Nov 2015 brief: organize the system "around principles from living systems" — [ceptr.org blog, 3 Nov 2015](https://ceptr.org/blog/2015-11-03-distributed-receptor-based-computing)
- Brock's GitHub bio: Ceptr is a rewrite "from the feminine reCEPTive capacity using the organizational patterns we find in nature" (search snippet only) — [github.com/artbrock](https://github.com/artbrock)
- MetaCurrency's broader living-systems frame: systems are "dynamic, living things" sustained by "the continued active exchange of value"; interrupting flows leaves "a lifeless collection of parts" — [metacurrency.org/about](https://metacurrency.org/about/)
- Harris-Braun's self-description on the MetaCurrency team page: "code monkey with an interest in meta-concepts, grammars, expressions, and receptors" — [metacurrency.org/team](https://metacurrency.org/team/)
- Holochain's later recap: Ceptr = "a nervous system for the globally connected world" — [blog.holochain.org](https://blog.holochain.org/play-with-a-mutual-credit-currency-and-join-the-modularity-discussion/)

### Inferences
- The "social DNA" / "social organism" language in the brief maps onto the Revelation's "each cell carries the instructions for cooperation" (code every node runs) and Noubel's "evolution of social organisms" (he is on the MetaCurrency team page).

### Gaps
- The Revelation's "CAS working paper" and "scape geometry" document are referenced but not available; the "Grammatic Capacities and the Evolution of Complex Adaptive Systems" draft (Brock & Harris-Braun) could not be fetched.

---

## Key Question 4: What funding/outreach attempts happened (grants, crowdfunding, conference pitches), with dates?

### Takeaway
No Kickstarter, crowdfunding campaign or named grant for Ceptr was found; through January 2017 the site said Ceptr was "funded by its team's work," outreach consisted of webinars, salons, hackathons and conference briefs (2014–2017), and the first outside money arrived in spring 2017 via a "Wealth Stewardship Circle" investment structure, with an ICO under exploration — i.e. the funding story is really the Holochain/Holo story.

### Cited Findings (chronological)
- Nov 20, 2009: IFTF FutureCast podcast with Brock on MetaCurrency (Jerry Michalski host) — [IFTF](https://legacy.iftf.org/future-now/article-detail/futurecast-jerry-michalski-interviews-arthur-brock-on-alternative-currencies/)
- Feb 28, 2011: Brock on a panel at the Future of Money & Technology Summit, SF; Oct 24, 2011: Occupy Wall Street "Re-Visioning Money Day" — [artbrock.com/deeper](https://www.artbrock.com/deeper)
- Oct 2011: MetaCurrency "Collabathon" on NextNet, ~50 attendees — [petervanstudios.com](http://petervanstudios.com/2011/10/31/metacurrency-collabathon-a-wealth-system/)
- Sep 15–16, 2014: Google Hangout On Air "What's been happening with the MetaCurrency project?" and the "Coming out of the MetaCurrency Closet" post; Sep 17, 2014: Revelation "pseudo-white-paper" released for feedback ("comments and feedback… are welcome!") — [ceptr.org blog](https://ceptr.org/blog/2014-09-16-hello-world), [ceptr.org blog](https://ceptr.org/blog/2014-09-16-the-ceptr-apocalypse)
- Apr 2, 2015: MIT/KIT webinar (Brock, Harris-Braun, Marc Clifton) in MIT's monthly emerging-web-technologies series — [ceptr.org blog, 1 Apr 2015](https://ceptr.org/blog/2015-04-01-mit-kit-webinar-april-2-2015), [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/); video posted Sep 25, 2015, "at the invitation of the MIT Kerboros Internet Technology group" — [ceptr.org blog](https://ceptr.org/blog/2015-09-24-mitkit-ceptr-webinar)
- Nov 3–4, 2015: brief submitted to Rebooting the Web of Trust, San Francisco — [ceptr.org blog](https://ceptr.org/blog/2015-11-03-distributed-receptor-based-computing)
- Jan 2016 ("January 2016 is a HUGE month for us" as they approach "the planned release of Ceptr"): Jan 20 Thrivable Future Salon at IFTF Palo Alto; Jan 25 "Ceptr Technology: Under the Hood" at Impact HUB Oakland; Jan 26–28 Deep Wealth Design workshop, Richmond CA; Jan 29 Living Wisdom Labs / Wealth Stewardship Circles (invitation only) — [ceptr.org blog, 21 Jan 2016](https://ceptr.org/blog/2016-01-21-january-2016-events-in-sfobay-area); the Oakland talk video/Prezi (prezi.com/raptqxuputwp/ceptr-tech-overview/) posted May 4, 2016 — [ceptr.org blog](https://ceptr.org/blog/2016-05-04-ceptr-under-the-hood)
- Jan 2017: ceptr.org states Ceptr is open source and "as of January 2017, funded by its team's work," noting this could change — [ceptr.org](http://ceptr.org/)
- Feb 21, 2017: Holochain dev sprint; March 2017 Holochain hackathon in San Francisco with open applications — [ceptr.org blog](https://ceptr.org/blog/2017-02-21-holochain_dev_sprint)
- May 2017: "Ceptr" registered on Idealist as a nonprofit at 4229 Moraga Street, San Francisco — [idealist.org](https://www.idealist.org/es/ong/2dbbecaa35804e2896fe91bc411b8e32-ceptr-san-francisco)
- Jun 9, 2017: "This Summer, Build the Next Internet!" residency call — teams in San Francisco, Albuquerque NM and Ashland OR; room and board; "an open-source project without a profit motive," most participants volunteers, a "do-acracy"; wants Go/JavaScript/protocol/blockchain skills plus storytellers, marketers, organizers — [P2P Foundation blog repost](https://blog.p2pfoundation.net/summer-build-next-internet/), [second repost](https://blog.p2pfoundation.net/65769-2/)
- Jun 12, 2017, Brock, "Organizational Phase Shift" (tagged Funding): MetaCurrency moving "from an informal open source project toward a scalable business," driven by funders' interest; "initial funds arrived in the weeks before the post" through a new investment structure giving investors upside while keeping resources open source; much of it "attracted through the Wealth Stewardship Circle model developed by Village Lab"; "a separate group is exploring an ICO to fund the next major development phase"; active team grew 6→12 with further doublings expected; summer roadmap = Holochain alpha, App Generator, multi-node test rig, Package Manager, DPKI, HC Index, Pluggable Governance, HC Cache; hackathons, virtual potlucks, internship/residency programs — [ceptr.org blog, 12 Jun 2017](https://ceptr.org/blog/2017-06-12-phase-shift)
- Harris-Braun's 2023 recollection: "In 2017, Brock and Harris-Braun said they had a blockchain-like technology to develop toward the Ceptr vision," after which Jean Russell joined Holo/Holochain — [Enacting Cybernetics](https://enacting-cybernetics.org/articles/10.58695/ec.2)

### Inferences
- The "2016 pivot" in the brief is better described as a Jan 2017 restructuring (announced 17 Jan 2017) in which the synchronization/data-integrity slice was extracted as Holochain and the rest of Ceptr effectively went into hiatus (the GitHub README later admits it "may look like it is on hiatus").
- Targeted searches for Ceptr + Kickstarter / Knight Foundation / crowdfunding returned nothing relevant; absence of evidence suggests no public crowdfunding campaign for Ceptr existed before the 2017 Holo ICO.

### Gaps
- Amounts and investor names for the spring-2017 funding are not stated anywhere found.
- Any grant applications (e.g., to foundations) between 2010 and 2016 are undocumented in accessible sources.

---

## Key Question 5: Who were the core contributors and what roles did they have?

### Takeaway
Ceptr was essentially a two-person architecture effort — Arthur Brock (concept, design, culture/currency framing, outreach) and Eric Harris-Braun ("zippy", principal coder of the C codebase and later Go Holochain prototype) — surrounded by the MetaCurrency Project circle (Ferananda Ibarra, Matthew Schutte, Jarod Holtz, Jean-François Noubel, Jeff Clearwater, Mary Camacho) and, by mid-2017, a dozen developers including Nicolas Luck ("Lucksus").

### Cited Findings
- Revelation and Pcubed/fractalvm whitepapers list authors as Arthur Brock and Eric Harris-Braun; Harris-Braun's GitHub handle is "zippy" — [ceptr.org/whitepapers/revelation](https://ceptr.org/whitepapers/revelation), [ceptr.org/whitepapers/protocols](https://ceptr.org/whitepapers/protocols)
- GitHub license credit: "The MetaCurrency Project (Eric Harris-Braun, Arthur Brock, et. al.)"; repo lives under zippy/ceptr with API docs at zippy.github.io/ceptr and a livecoding.tv/zippy channel — [github.com/zippy/ceptr](https://github.com/zippy/ceptr)
- All 19 ceptr.org blog posts (2014–2017) are authored by Brock (vision, events, design essays) or Harris-Braun (the "Musings on Coding in Ceptr" dev series, Semantic Trees, restructuring, Holochain sprint) — [ceptr.org/blog](https://ceptr.org/blog/)
- Harris-Braun bio: "designs and builds software infrastructure for the new economy"; co-founder MetaCurrency; core developer of Ceptr; lead developer of Flowplace (Collective Intelligence Research Institute); co-founder Glass Bead Software and Harris-Braun Enterprises; published *The Internet Directory* (1994, >100,000 copies); B.S. CS Yale; advisory board, Schumacher Center for New Economics — [P2P Foundation wiki](https://wiki.p2pfoundation.net/Eric_Harris-Braun), [Schumacher Center](https://centerforneweconomics.org/?p=126)
- Marc Clifton co-presented the Apr 2, 2015 MIT/KIT webinar with Brock and Harris-Braun — [prezi.com](https://prezi.com/y_7109dt0gzj/just-a-spoonful-of-ceptr/)
- metacurrency.org team page: Arthur Brock ("culture hacker, software architect, and alt.Currency geek"), Jean-François Noubel (collective intelligence / evolution of social organisms), Jarod Holtz, Eric Harris-Braun, Ferananda [Ibarra] ("currency designer in the making," facilitation), Matthew Schutte (political philosopher, privacy advocate) — [metacurrency.org/team](https://metacurrency.org/team/)
- Ferananda Ibarra and Alan Rosenblith produced the 2009 MetaCurrency intro video — [P2P Foundation wiki](https://wiki.p2pfoundation.net/Arthur_Brock_and_Eric_Harris-Braun%27s_Introduction_to_The_MetaCurrency_Project)
- June 2017 roster (Brock): developers DayZee (Docker/multi-node gossip testing), Timotree3 (cleanup, security), Neonphog (app scaffolding wizard), Lucksus (core, message flows, security, "working with Zippy"); business/ops: Arthur Brock, Mary Camacho (leadership), Matthew Schutte (residency workspace), Jarod Holtz (admin/support), Ferananda Ibarra and Jeff Clearwater (Village Lab funding) — [ceptr.org blog, 12 Jun 2017](https://ceptr.org/blog/2017-06-12-phase-shift)
- "Lucksus" is Nicolas Luck, later described as a Holochain core developer (search snippet only) — [awesome.ecosyste.ms Holochain list](https://awesome.ecosyste.ms/lists/23963)
- Matthew Schutte later appears as a Holochain/Holo spokesperson (podcast "The Evolution of Community, Economy, and the Internet with Matthew Schutte") — [spreaker.com](https://www.spreaker.com/episode/18364034)
- Brock is billed "Founder of Holochain & Ceptr" (Feb 2018 Curiosity Talk) — [redefineschool.com](https://redefineschool.com/arthur-brock/)

### Inferences
- Brock's role was architect/visionary and public voice (all vision posts, whitepaper lead author, culture/currency framing); Harris-Braun's was implementation lead (C codebase, Semtrex, Holochain Go prototype). The MetaCurrency circle (Ibarra, Schutte, Holtz, Clearwater, Camacho) handled facilitation, funding and operations rather than Ceptr code.

### Gaps
- Matthew Brisebois and Jarod Luebbert: no source connecting either to Ceptr or MetaCurrency was found (the Jarod on the team is Jarod Holtz). Nicolas Luck's involvement is only documented from 2017 (Holochain phase).
- The GitHub contributors list for zippy/ceptr could not be read (API access disabled), so the full code-contributor roster (and whether Marc Clifton or others committed) is unverified.
- The pre-2017 ceptr.org "people/team" page (Wayback) could not be retrieved.

---

## Consolidated chronology (all items sourced above)
- 2001 – Brock's Dream Team Technologies wins Colorado Ethics in Business Award (artbrock.com/deeper)
- c. 2003–04 – Brock and Harris-Braun active on Omidyar.net (Enacting Cybernetics)
- May 2009 – MetaCurrency intro video with Brock/Harris-Braun circulating (P2P wiki); Nov 20, 2009 – IFTF FutureCast with Brock, MetaCurrency described as Brock (ex-OS-Earth) + Harris-Braun (Open Money) (IFTF)
- 2009–2011 – metacurrency.org "four opens" (Open Identity/Rules/Transport/Data) (P2P wiki quoting metacurrency.org); Flowplace downloadable 2009 (search snippet)
- Feb & Oct 2011 – Future of Money & Technology Summit; OWS Re-Visioning Money Day (artbrock.com)
- Oct 2011 – NextNet Collabathon: five-layer ladder, "self-describing computing" (petervanstudios.com)
- c. 2010–2013 – Ceptr design/coding begins ("past 5 years" in Nov 2015; 2013 copyright) (ceptr.org blog; GitHub)
- Summer 2012 – Emerging Leader Labs incubator run by Brock & Harris-Braun (artbrock.com)
- Sep 16–17, 2014 – Public launch: "Coming out of the MetaCurrency Closet"; Ceptr Revelation draft (ceptr.org blog)
- Nov 2014 – Strange Loop, Receptive Capacity Breakthrough, Semantic Alternation posts (ceptr.org blog)
- Apr 2, 2015 – MIT/KIT webinar (Brock, Harris-Braun, Clifton) (ceptr.org blog; Prezi)
- Nov 3–4, 2015 – Rebooting the Web of Trust brief (ceptr.org blog)
- Jan 2016 – Bay Area event series ahead of "planned release of Ceptr" (ceptr.org blog)
- Mar–Jul 2016 – Harris-Braun "Musings on Coding in Ceptr" series (ceptr.org blog)
- Jan 17, 2017 – Restructured into Holochain, Pcubed, ceptr-core (+ Holo, Sovereign Commons, Neural Internetworking on site); new website; "funded by its team's work" (ceptr.org blog; ceptr.org)
- Feb–Mar 2017 – Holochain dev sprint and SF hackathon (ceptr.org blog)
- May–Jun 2017 – Idealist nonprofit listing; summer residency call; "Organizational Phase Shift": first outside funding via Wealth Stewardship Circle, ICO exploration, team 6→12 (idealist.org; P2P blog; ceptr.org blog)
- 2020 retrospective – Holochain blog: "roughly a decade" of MetaCurrency work preceded releasing one Ceptr component as Holochain (blog.holochain.org)
