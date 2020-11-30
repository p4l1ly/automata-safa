let SessionLoad = 1
let s:so_save = &so | let s:siso_save = &siso | set so=0 siso=0
let v:this_session=expand("<sfile>:p")
silent only
cd ~/school/afasat_related/afabuild
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
set shortmess=aoO
badd +55 src/model/Afa/Term/Mix.hs
badd +1 term://.//871530:/bin/zsh
badd +6 cabal.project.local
badd +21 hie.yaml
badd +23 automata-safa.cabal
badd +43 src/model/Afa/Term/Bool.hs
badd +20 src/model/Afa/Lib.hs
badd +124 src/model/Afa/Bool.hs
badd +19 src/model/Afa.hs
badd +28 src/model/Afa/Lib/Tree.hs
badd +1 src/model/Afa/Ops/Preprocess.hs
badd +9 src/convert/Afa/Convert/Capnp/Afa.hs
badd +58 src/model/Afa/Term/Bool/Simplify.hs
badd +169 ~/hobby/lens-recursion-schemes/test/Test/Afa.hs
badd +1 test/Test/Afa/Simplify.hs
badd +157 ~/hobby/lens-recursion-schemes/src/Control/RecursionSchemes/Lens.hs
argglobal
%argdel
edit src/model/Afa/Bool.hs
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
2wincmd h
wincmd w
wincmd w
set nosplitbelow
set nosplitright
wincmd t
set winminheight=0
set winheight=1
set winminwidth=0
set winwidth=1
exe 'vert 1resize ' . ((&columns * 126 + 190) / 381)
exe 'vert 2resize ' . ((&columns * 127 + 190) / 381)
exe 'vert 3resize ' . ((&columns * 126 + 190) / 381)
argglobal
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 49 - ((24 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
49
normal! 042|
wincmd w
argglobal
if bufexists("src/model/Afa/Lib/Tree.hs") | buffer src/model/Afa/Lib/Tree.hs | else | edit src/model/Afa/Lib/Tree.hs | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let s:l = 2 - ((1 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
2
normal! 0
wincmd w
argglobal
if bufexists("term://.//871530:/bin/zsh") | buffer term://.//871530:/bin/zsh | else | edit term://.//871530:/bin/zsh | endif
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
let s:l = 994 - ((72 * winheight(0) + 36) / 73)
if s:l < 1 | let s:l = 1 | endif
exe s:l
normal! zt
994
normal! 076|
wincmd w
exe 'vert 1resize ' . ((&columns * 126 + 190) / 381)
exe 'vert 2resize ' . ((&columns * 127 + 190) / 381)
exe 'vert 3resize ' . ((&columns * 126 + 190) / 381)
tabnext 1
if exists('s:wipebuf') && getbufvar(s:wipebuf, '&buftype') isnot# 'terminal'
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20 winminheight=1 winminwidth=1 shortmess=filnxtToOFc
let s:sx = expand("<sfile>:p:r")."x.vim"
if file_readable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &so = s:so_save | let &siso = s:siso_save
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
