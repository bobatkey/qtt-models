{
  description = "Theory and Applications of Quantitative Type Theory";
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.05;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    with flake-utils.lib; eachSystem allSystems (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            # https://tug.org/texlive/devsrc/Master/doc.html
            scheme-minimal latex-bin latexmk acmart
            xkeyval xstring amscls amsmath microtype
            etoolbox booktabs refcount ltxcmds infwarerr
            totpages environ textcase natbib hyperref
            pdftexcmds kvoptions hyperxmp ifmtarg oberdiek
            xcolor geometry ncctools cmap caption float
            comment fancyhdr preprint epstopdf-pkg
            libertine inconsolata newtx upquote txfonts
            # Additional packages beyond those required for acmart
            mdwtools stmaryrd semantic tcolorbox pgf
            latex-tools-dev listings quoting mathpartir multirow sttools
            cmll
            # needed for workingnote
            ntheorem mathtools todonotes titlesec bbold bbold-type1
            tex-gyre;
        };
        agda = pkgs.agda.withPackages (ps: [ ps.standard-library ]);
      in rec {
        packages = rec {
          default = paper;
          paper = pkgs.stdenvNoCC.mkDerivation rec {
            name = "paper";
            src = self;
            buildInputs = [ pkgs.coreutils pkgs.gnumake pkgs.bash tex ];
            phases = ["unpackPhase" "buildPhase" "installPhase"];
            buildPhase = "make paper/paper.pdf";
            installPhase = ''
      mkdir -p $out;
      cp paper/paper.pdf $out/
    '';
          };
          supplementary-material = pkgs.stdenvNoCC.mkDerivation rec {
            name = "supplementary-material";
            src = self;
            buildInputs = [ agda ];
            phases = [ "unpackPhase" "buildPhase" "installPhase" ];
            buildPhase = ''
mkdir -p html;
agda --html --html-dir=html src/Everything.agda;
find src/ -name '*.agdai' | xargs rm;
'';
            installPhase = ''
mkdir -p $out;
cp -R src $out/;
cp poly-time.agda-lib $out/;
cp supplementary/README $out/README;
mkdir -p $out/html;
cp html/* $out/html;
'';
          };
        };

        devShells.default = pkgs.mkShell {
          # Get the build inputs from all of the packages defined above
          inputsFrom = builtins.attrValues packages;
        };
      });
}
