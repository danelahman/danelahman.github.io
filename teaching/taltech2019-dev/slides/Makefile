# This uses Madoko (https://madoko.codeplex.com/)

deck:
	@madoko talk.mdk --odir=out/talk | grep -v "warning: unable to read language definition" | true

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -dfr math
