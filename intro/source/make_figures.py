"""Draw the additional explanatory SVGs; Python standard library only."""
from pathlib import Path
from html import escape

OUT = Path(__file__).parent / 'figures'
INK, GRAY, LIGHT, BLUE = '#1C1B1A', '#6F6E69', '#CECDC3', '#1A4F8C'

class Figure:
    def __init__(self, name, height, title):
        self.name = name
        self.parts = [f'<svg xmlns="http://www.w3.org/2000/svg" role="img" width="680" height="{height}" viewBox="0 0 680 {height}" font-family="-apple-system, BlinkMacSystemFont, system-ui, sans-serif">', f'<title>{escape(title)}</title>']
    def text(self, x, y, s, size=18, color=INK, anchor='middle'):
        self.parts.append(f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-size="{size}" fill="{color}">{escape(s)}</text>')
    def line(self, x1,y1,x2,y2,color=GRAY,width=1.5,dash=''):
        self.parts.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{color}" stroke-width="{width}"'+(f' stroke-dasharray="{dash}"' if dash else '')+'/>')
    def path(self, d, color=GRAY, width=1.5, fill='none'):
        self.parts.append(f'<path d="{d}" stroke="{color}" stroke-width="{width}" fill="{fill}"/>')
    def rect(self,x,y,w,h,fill='none',stroke=LIGHT):
        self.parts.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{fill}" stroke="{stroke}"/>')
    def circle(self,x,y,r=5,fill=BLUE):
        self.parts.append(f'<circle cx="{x}" cy="{y}" r="{r}" fill="{fill}"/>')
    def arrow(self,x1,y1,x2,y2,color=GRAY):
        self.line(x1,y1,x2,y2,color)
        if x1==x2:
            self.path(f'M{x2-5} {y2-7}L{x2} {y2}L{x2+5} {y2-7}',color)
        else:
            self.path(f'M{x2-7} {y2-5}L{x2} {y2}L{x2-7} {y2+5}',color)
    def save(self):
        (OUT/(self.name+'.svg')).write_text('\n'.join(self.parts+['</svg>'])+'\n',encoding='utf-8', newline='\n')

f=Figure('pauli-signs',265,'Commutation is a parity calculation. XX and ZZ exchange X and Z on two qubits and commute; XI and ZI exchange them on one qubit and anticommute.')
for cx,title in [(175,'Two local exchanges'),(505,'One local exchange')]:
    f.text(cx,30,title,20)
for x,labels in [(105,('X','Z')),(235,('X','Z')),(435,('X','Z')),(565,('I','I'))]:
    f.rect(x-34,58,68,111)
    f.text(x,89,labels[0],25); f.text(x,147,labels[1],25)
    if labels[0]=='X':
        f.path(f'M{x-20} 102L{x+20} 121 M{x+20} 102L{x-20} 121',BLUE,2)
        f.text(x,193,'one minus',15,BLUE)
    else: f.text(x,193,'no sign',15,GRAY)
f.text(175,237,'Even parity: commute',19,BLUE)
f.text(505,237,'Odd parity: anticommute',19,BLUE)
f.save()

f=Figure('carrier-evaluation',440,'Evaluate a carrier at a fixed visible word. Outside the support envelope the amplitude is zero. Inside, enumerate the bound alternatives, read their phases, sum them and multiply by the scalar and the normalization factor. The illustrated two alternatives are the case of one bound bit.')
f.text(340,27,'Read one amplitude from the record',22)
f.rect(40,56,265,53); f.text(172,89,'Fix a visible word',19)
f.arrow(305,82,369,82)
f.rect(370,56,270,53); f.text(505,78,'Test the support envelope',18); f.text(505,99,'using geometry and offset',15,GRAY)
f.arrow(505,109,505,148)
f.text(555,135,'outside',15,GRAY)
f.text(505,171,'Amplitude zero',19,GRAY)
f.path('M370 92H340V196H300',GRAY)
f.text(315,159,'inside',15,GRAY)
f.rect(40,183,260,78)
f.text(170,205,'Read each bound alternative',17)
f.circle(108,234,12,'#E6E4D9'); f.text(108,240,'0',17)
f.circle(226,234,12,'#E6E4D9'); f.text(226,240,'1',17)
f.arrow(300,223,369,223)
f.rect(370,190,270,65); f.text(505,217,'Evaluate its phase',19); f.text(505,240,'from polynomial and precision',15,GRAY)
f.path('M505 255V285H170V308',GRAY)
f.rect(40,309,260,57); f.text(170,342,'Add the phases',19,BLUE)
f.arrow(300,337,369,337)
f.rect(370,309,270,57); f.text(505,332,'Apply scale and',18); f.text(505,353,'bound-bit normalization',18)
f.arrow(505,366,505,399)
f.text(505,425,'One complex amplitude',19,BLUE)
f.text(170,409,'Repeat for each visible word',15,GRAY)
f.save()

f=Figure('carrier-gates',440,'Three gate effects. A diagonal gate changes the phase of a permitted word, illustrated by Z on a Bell pair. CNOT relabels its permitted words from 00 and 11 to 00 and 10. A free Hadamard introduces a summed alternative, illustrated by interference turning a plus state into zero.')
f.text(340,26,'Three ways to transform a carrier',22)
for y in [48,174,300]: f.line(35,y,645,y,LIGHT)
f.text(52,80,'Diagonal',20,INK,'start'); f.text(52,107,'Change phases',16,GRAY,'start')
for x,label in [(303,'00'),(511,'11')]:
    f.rect(x-40,66,80,40); f.text(x,94,label,22)
f.text(303,137,'phase unchanged',15,GRAY); f.text(511,137,'phase negated by Z',15,BLUE)
f.text(52,208,'CNOT',20,INK,'start'); f.text(52,235,'Relabel words',16,GRAY,'start')
for y,a,b in [(210,'00','00'),(257,'11','10')]:
    f.text(303,y,a,22); f.arrow(351,y-7,462,y-7,BLUE); f.text(511,y,b,22,BLUE)
f.text(52,335,'Hadamard',20,INK,'start'); f.text(52,362,'Mix alternatives',16,GRAY,'start')
f.text(292,330,'output zero',16,GRAY); f.text(510,330,'output one',16,GRAY)
f.text(292,363,'+    +',24,BLUE); f.text(510,363,'+    −',24,GRAY)
f.text(292,398,'reinforce',17,BLUE); f.text(510,398,'cancel',17,GRAY)
f.text(340,433,'Gate action changes the state; a rewrite changes its presentation',15,GRAY)
f.save()

f=Figure('interference',315,'Two Hadamards return an initial zero qubit to zero. Both intermediate paths contribute positively to output zero; their contributions to output one have opposite signs and cancel.')
f.text(65,30,'Input',19); f.text(315,30,'Summed bit',19); f.text(565,30,'Output',19)
f.text(185,58,'first H',16,GRAY); f.text(440,58,'second H',16,GRAY)
for x,y,label in [(65,159,'0'),(315,95,'0'),(315,225,'1'),(565,95,'0'),(565,225,'1')]:
    f.circle(x,y,19,'#fff'); f.text(x,y+7,label,23)
for y in [95,225]: f.line(90,155,290,y,GRAY)
for ya,yb,col in [(95,95,BLUE),(225,95,BLUE),(95,225,GRAY),(225,225,GRAY)]: f.line(339,ya,541,yb,col,2)
f.text(450,87,'+',22,BLUE); f.text(450,149,'+',22,BLUE)
f.text(395,157,'+',22,GRAY); f.text(450,250,'−',22,GRAY)
f.text(315,291,'Add amplitudes before taking probabilities',19,BLUE)
f.text(610,100,'add',16,BLUE); f.text(610,230,'cancel',16,GRAY)
f.save()

f=Figure('unread-bell',280,'The retained Bell qubit is correlated with an unread qubit. The unread states zero and one are orthogonal, so cross terms vanish and the retained density matrix has only two equal diagonal entries.')
f.text(167,29,'Bell correlations',20); f.text(505,29,'Retained density matrix',20)
f.text(78,65,'kept',16,GRAY); f.text(253,65,'unread',16,GRAY)
for y,bit in [(113,'0'),(193,'1')]:
    f.text(78,y,bit,25); f.line(107,y-7,224,y-7,BLUE,2); f.text(253,y,bit,25)
f.text(168,249,'Different unread states',16,GRAY)
f.arrow(304,151,360,151)
for i in range(2):
    for j in range(2):
        x,y=421+j*80,70+i*80
        f.rect(x,y,72,72, BLUE if i==j else '#E6E4D9','none')
        f.text(x+36,y+45,'½' if i==j else '0',25,'#fff' if i==j else GRAY)
f.text(500,249,'Cross terms vanish',18,BLUE)
f.save()

f=Figure('chains',295,'A filled square has four boundary edges. Taking their boundary counts each corner twice, leaving zero over binary arithmetic. This is the geometric reason a boundary has no syndrome.')
f.text(105,30,'A face',20); f.text(335,30,'Its boundary',20); f.text(575,30,'Boundary again',20)
f.rect(48,85,112,112,'#E6E4D9',LIGHT)
f.rect(278,85,112,112,'none',BLUE)
for x in [48,160,278,390]:
    for y in [85,197]: f.circle(x,y,4,GRAY)
f.arrow(185,142,252,142); f.arrow(414,142,479,142)
for x in [520,630]:
    for y in [85,197]:
        f.circle(x,y,7,BLUE); f.text(x,y+31,'twice',15,GRAY)
f.text(105,262,'2-dimensional cell',16,GRAY)
f.text(335,262,'1-dimensional chain',16,GRAY)
f.text(575,262,'Zero modulo two',17,BLUE)
f.save()

f=Figure('surface-patch',390,'Two copies of the unrotated distance-three planar patch. Each has thirteen edge qubits: nine vertical and four interior horizontal. A four-edge loop bounds a face and is a stabilizer; a three-edge vertical string joins the rough boundaries and is a logical Z. Dashed boundary guides are not data-qubit edges.')
for off,title in [(25,'A stabilizer boundary'),(365,'A logical string')]:
    f.text(off+145,28,title,20)
    for j in range(3):
        x=off+45+j*100
        f.line(x,85,x,285,LIGHT)
        for k in range(3): f.circle(x,85+(k+0.5)*200/3,4,GRAY)
    for j in [1,2]:
        y=85+j*200/3
        f.line(off+45,y,off+245,y,LIGHT)
        for k in range(2): f.circle(off+95+k*100,y,4,GRAY)
    f.line(off+30,85,off+260,85,INK,1.5,'5 4')
    f.line(off+30,285,off+260,285,INK,1.5,'5 4')
    f.text(off+145,65,'rough boundary',16,GRAY)
    f.text(off+145,312,'rough boundary',16,GRAY)
f.path('M70 151.667H170V218.333H70Z',BLUE,4)
f.path('M510 85V285',BLUE,4)
for x,y in [(120,151.667),(120,218.333),(70,185),(170,185),(510,118.333),(510,185),(510,251.667)]:
    f.circle(x,y,5,BLUE)
f.text(170,354,'Bounds a collection of faces',17,BLUE)
f.text(510,354,'Joins distinct rough boundaries',17,BLUE)
f.text(340,384,'Dots mark data qubits; dashed lines mark boundary guides',15,GRAY)
f.save()

f=Figure('surface-roadmap',520,'Selected plan targets. Proved foundations include surface-code geometry, encoding and Pauli errors. Planned syndrome extraction and correction lead toward the surface-code memory theorem. Further planned work includes noisy rounds, detector models and lattice surgery. This is a reading guide, not the complete dependency graph.')
f.text(340,28,'From a code to a verified memory',22)
rows=[(60,'PROVED','Geometry and distance · encoding · Pauli errors','T34 · T29 · T64',True),
      (168,'PLANNED','Syndrome extraction and decoder-controlled correction','T30 · T31',False),
      (276,'PLANNED','One-round surface-code memory theorem','T65',False),
      (411,'FURTHER WORK','Noisy rounds and detectors · lattice surgery','T53 · T61',False)]
for y,status,label,ids,done in rows:
    f.rect(40,y,600,76,'none',INK if done else LIGHT)
    f.circle(61,y+21,5,INK if done else '#fff')
    if not done: f.rect(56,y+16,10,10,'none',GRAY)
    f.text(82,y+26,status,14,GRAY,'start')
    f.text(620,y+26,ids,14,GRAY,'end')
    f.text(340,y+56,label,18,INK)
f.arrow(340,136,340,168); f.arrow(340,244,340,276)
f.text(340,389,'The programme then extends to repeated operations',16,GRAY)
f.text(340,514,'Status from the plan inspected on 5 October 2026',14,GRAY)
f.save()
