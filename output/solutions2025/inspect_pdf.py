from pathlib import Path
from pypdf import PdfReader
import pypdfium2 as pdfium
from PIL import Image,ImageOps,ImageDraw
p=Path('output/solutions2025/2025_Mathematics_Solutions.pdf')
r=PdfReader(p)
print('Pages:',len(r.pages))
for i,pg in enumerate(r.pages):
    t=pg.extract_text()
    print(i+1,len(t),t.splitlines()[0], 'bad glyphs:',t.count('\u25a0')+t.count('\ufffd'))
d=pdfium.PdfDocument(p)
thumbs=[]
renderdir=Path('tmp/pdfs/output');renderdir.mkdir(exist_ok=True)
for i,page in enumerate(d):
    im=page.render(scale=1.4).to_pil();im.save(renderdir/f'page-{i+1:02}.png')
    im.thumbnail((298,422)); tile=Image.new('RGB',(318,452),'#dfe5eb');tile.paste(im,((318-im.width)//2,12));ImageDraw.Draw(tile).text((12,433),str(i+1),fill='black');thumbs.append(tile)
for start in range(0,len(thumbs),6):
    canvas=Image.new('RGB',(318*3,452*2),'white')
    for k,im in enumerate(thumbs[start:start+6]):canvas.paste(im,((k%3)*318,(k//3)*452))
    canvas.save(renderdir/f'contact-{start//6+1}.png')
