# Project-local, incremental pdfLaTeX build. TikZ's own content hashes rebuild
# changed drawings; the context check also catches shared fonts and styles.
use Digest::SHA qw(sha256_hex);
use File::Path qw(make_path);

$pdf_mode = 1;
$pdflatex = 'pdflatex -shell-escape %O %S';
$max_repeat = 5;
make_path('build/tikz');

sub paper_read {
    my ($path) = @_;
    return '' unless -f $path;
    open my $in, '<:raw', $path or die "Cannot read $path: $!";
    local $/;
    return <$in>;
}
sub paper_write_if_changed {
    my ($path, $content) = @_;
    return if -f $path && paper_read($path) eq $content;
    open my $out, '>:raw', $path or die "Cannot write $path: $!";
    print $out $content;
    close $out;
}

my $context = paper_read('preamble.tex');
my $main = -f 'queens.tex' ? 'queens.tex' : 'paper.tex';
$context .= (split /\n/, paper_read($main))[0];
for my $path (sort(glob('sections/*.tex'), glob('figures/*.tex'))) {
    # These settings also occur outside a tikzpicture, where TikZ's picture
    # hash cannot see them. Ordinary prose changes do not invalidate drawings.
    for my $line (split /\n/, paper_read($path)) {
        $context .= "$path:$line\n" if $line =~ /^\s*\\(?:definecolor|setboardfontsize|tikzset|tikzstyle)\b/;
    }
}
my $digest = sha256_hex($context);
if (paper_read('build/tikz-context.sha256') ne $digest) {
    # Only remove checksum files in this explicit cache directory. Missing
    # hashes make TikZ rebuild its PDFs; no manuscript files are removed.
    unlink glob('build/tikz/*.md5');
    paper_write_if_changed('build/tikz-context.sha256', $digest);
}
my $settings = $ENV{'QUEENS_NO_CACHE'}
    ? "% TikZ cache disabled for this build.\n"
    : "\\usetikzlibrary{external}\n\\tikzexternalize[prefix=build/tikz/]\n";
paper_write_if_changed('build/tikz-settings.tex', $settings);
