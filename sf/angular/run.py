"""Angular tomography: saved figures and consistency checks."""
import os
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'
os.environ.setdefault('MPLBACKEND', 'Agg')
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import sys
if not __package__:
    sys.path[0] = str(Path(__file__).resolve().parents[2])
    __package__ = 'sf.angular'
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm, to_rgb
from matplotlib.font_manager import fontManager
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, Ellipse, FancyArrowPatch, Polygon
from matplotlib.path import Path as MplPath
from matplotlib.ticker import NullLocator
from scipy.special import sph_harm_y
from PIL import Image
import pymupdf as fitz
from .physics import FIELD, GRIDS, RATIOS, ThermalSystem, angular_grid, decompose, ideal

HERE = Path(__file__).resolve().parent
DATA, RUNS = HERE/'data', HERE.parents[1]/'runs/sf/angular'
FAMILIES, ORDERS = ('square', 'honeycomb'), (2, 3, 4)
MODELS = ((2, '#C2DFF1'), (3, '#8EC4E4'), (4, '#559FCE'))
STEMS = ('square_compass', 'honeycomb_kitaev')


def digest(path):  # Check saved input hashes.
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check(directory=DATA, physics=False):  # Replay harmonics; optionally recompute thermal traces.
    directory = Path(directory)
    settings = json.loads((directory/'settings.json').read_text())
    if directory.resolve() == DATA.resolve():
        for name, record in settings['source_files'].items():
            assert digest(directory/name) == record['sha256'], f'Changed input: {name}'
    assert digest(directory/'artwork.pdf') == settings['artwork_sha256']
    with np.load(directory/'ideal.npz') as data:
        for key, value in ideal().items():
            np.testing.assert_allclose(value, data[key], atol=3e-12, rtol=0)
        for i, order in enumerate(ORDERS):
            assert np.max(data['amplitudes'][i, order+1:]) < 1e-11
    with np.load(directory/'thermal.npz') as data:
        assert int(data['n']) == 12 and float(data['field']) == FIELD
        np.testing.assert_allclose(data['temperature_over_B'], RATIOS, atol=1e-15, rtol=0)
        assert len(RATIOS) == 26 and np.count_nonzero(RATIOS == .1) == 1
        for grid, shape in GRIDS.items():
            directions, theta, phi, weights = angular_grid(*shape)
            np.testing.assert_allclose(directions, data[grid+'_directions'], atol=1e-14)
            np.testing.assert_allclose(weights, data[grid+'_weights'], atol=1e-14)
            for family in FAMILIES:
                prefix = family+'_'+grid
                signal = data[prefix+'_signal']
                assert signal.shape == (3, 26, len(directions)) and np.isfinite(signal).all()
                coefficients, amplitudes, lm = decompose(signal, theta, phi, weights)
                for suffix, value in [('coefficients', coefficients), ('amplitudes', amplitudes)]:
                    np.testing.assert_allclose(value, data[prefix+'_'+suffix], atol=1e-11, rtol=0)
                np.testing.assert_array_equal(lm, data['lm'])
        for family in FAMILIES:
            assert np.max(abs(data[family+'_fine_coefficients']-data[family+'_coarse_coefficients'])) < 1e-4
            if physics:
                system = ThermalSystem(family)
                for i, order in enumerate(ORDERS):
                    result = system.evaluate(order, data['fine_directions'][0])
                    for key in ('signal', 'polarization'):
                        np.testing.assert_allclose(result[key], data[family+'_fine_'+key][i, :, 0], atol=1e-9, rtol=0)
    print('PASS: ideal polynomials and both thermal lattices; 26 temperatures, 288/512 directions.')
    if physics:
        print('PASS: six freshly diagonalized N=12 thermal traces agree with the saved data.')


def fonts():  # Prefer the paper fonts; retain portable fallbacks.
    available = {font.name for font in fontManager.ttflist}
    return dict(title='Avenir' if 'Avenir' in available else 'DejaVu Sans',
                serif='Times New Roman' if 'Times New Roman' in available else 'STIXGeneral')


def view_basis():  # Keep the original sphere camera.
    az, el = np.radians([-55, 22])
    front = np.array([np.cos(el)*np.cos(az), np.cos(el)*np.sin(az), np.sin(el)])
    right = np.array([-np.sin(az), np.cos(az), 0.])
    return front, right, np.cross(front, right)


def sphere_directions(edge=1.01):  # Map image pixels onto the visible hemisphere.
    axis = np.linspace(-edge, edge, 500)
    x, y = np.meshgrid(axis, axis)
    radius = x*x+y*y
    mask = radius <= 1
    front, right, up = view_basis()
    directions = x[mask,None]*right+y[mask,None]*up+np.sqrt(1-radius[mask,None])*front
    return mask, directions


def harmonic_values(coefficients, lm, directions):  # Evaluate interpolants in bounded-memory batches.
    theta = np.arccos(np.clip(directions[:,2], -1, 1))
    phi = np.arctan2(directions[:,1], directions[:,0])
    values = np.empty((*coefficients.shape[:-1], len(directions)), complex)
    for start in range(0, len(directions), 4096):
        stop = start+4096
        basis = sph_harm_y(lm[:,0,None], lm[:,1,None], theta[None,start:stop], phi[None,start:stop])
        values[...,start:stop] = coefficients @ basis
    assert np.max(abs(values.imag)) < 1e-10
    return values.real


def graticule(ax):  # Draw only the visible latitude and longitude arcs.
    front, right, up = view_basis()
    def line(points):  # Hide arcs behind the sphere.
        visible = points @ front >= 0
        ax.plot(np.where(visible, points @ right, np.nan), np.where(visible, points @ up, np.nan),
                color='#344854', alpha=.18, lw=.3)
    t = np.linspace(0, 2*np.pi, 501)
    for latitude in (-60, -30, 0, 30, 60):
        z, radius = np.sin(np.radians(latitude)), np.cos(np.radians(latitude))
        line(np.c_[radius*np.cos(t), radius*np.sin(t), np.full_like(t,z)])
    p = np.linspace(0, np.pi, 401)
    for longitude in np.arange(0, 360, 45):
        a = np.radians(longitude)
        line(np.c_[np.sin(p)*np.cos(a), np.sin(p)*np.sin(a), np.cos(p)])
    ax.add_patch(Circle((0,0), 1, fill=False, lw=.45, edgecolor='#526A7A'))


def field_rotation_cue(ax):  # Shade the field arrow and draw its scan arc.
    front, right, up = view_basis()
    direction = -.63*right+.50*up+.59*front
    direction /= np.linalg.norm(direction)
    side = np.cross(direction, front)
    side /= np.linalg.norm(side)
    transverse = np.cross(direction, side)
    project = lambda points: np.column_stack((points @ right, points @ up))
    light = -.45*right+.65*up+.75*front
    light /= np.linalg.norm(light)
    gold = np.asarray(to_rgb('#D8A326'))
    phi = np.linspace(0, 2*np.pi, 25)
    radial = np.cos(phi)[:, None]*side+np.sin(phi)[:, None]*transverse
    faces = []

    def face(points, normal, ghost=False):  # Shade and depth-sort one arrow face.
        normal = normal/np.linalg.norm(normal)
        if ghost and normal @ front <= 0:
            return
        color = np.clip(gold*(.64+.36*max(0., normal @ light))+.025, 0, 1)
        faces.append((float(points.mean(axis=0) @ front), project(points), color, ghost))

    radius, neck, length, head_radius = .016, 1.36, 1.62, .057
    for start, stop, ghost in ((.06, 1., True), (1., neck, False)):
        lower, upper = start*direction+radius*radial, stop*direction+radius*radial
        for index in range(24):
            face(np.array([lower[index], lower[index+1], upper[index+1], upper[index]]),
                 radial[index]+radial[index+1], ghost)
    rim = neck*direction+head_radius*radial
    for index in range(24):
        normal = radial[index]+radial[index+1]
        normal /= np.linalg.norm(normal)
        face(np.array([rim[index], rim[index+1], length*direction]),
             normal+head_radius/(length-neck)*direction)
    face(rim[:-1], -direction)

    exit_point = project(direction[None])[0]
    ax.add_patch(Ellipse(exit_point, .075, .075*abs(direction @ front),
                        angle=np.degrees(np.arctan2(exit_point[1], exit_point[0]))+90,
                        facecolor='#6D571F', edgecolor='none', alpha=.12, zorder=3,
                        clip_on=False))
    for _, points, color, ghost in sorted(faces, key=lambda item: item[0]):
        ax.add_patch(Polygon(points, facecolor=color, edgecolor='none',
                             alpha=.24 if ghost else 1., zorder=.7 if ghost else 5,
                             clip_on=False))

    angles = np.radians(np.linspace(195, 150, 50))
    arc = 1.18*np.column_stack((np.cos(angles), np.sin(angles)))
    ax.add_patch(FancyArrowPatch(path=MplPath(arc), arrowstyle='->', mutation_scale=4.5,
                                color='#617D90', lw=.55, zorder=4, clip_on=False))
    ax.text(-.85, .91, r'$B\hat n$', fontsize=8., ha='center', va='center',
            math_fontfamily='stix', zorder=6, clip_on=False)


def main_figure(data, output):  # Rescale whole Hamiltonians to equal total harmonic amplitude.
    names = fonts()
    plt.rcParams.update({'font.family':'sans-serif', 'font.sans-serif':[names['title']],
        'mathtext.fontset':'dejavusans', 'font.size':8, 'axes.labelsize':8.5,
        'axes.titlesize':9, 'xtick.labelsize':8, 'ytick.labelsize':8,
        'axes.labelcolor':'black', 'xtick.color':'black', 'ytick.color':'black',
        'text.color':'black', 'axes.edgecolor':'#23252F', 'axes.linewidth':.65,
        'pdf.fonttype':42, 'figure.facecolor':'white', 'savefig.facecolor':'white', 'savefig.bbox':None})
    totals = data['amplitudes'][:,1:].sum(axis=1)
    scales = totals[0]/totals
    amplitudes = scales[:,None]*data['amplitudes']
    np.testing.assert_allclose(amplitudes[:,1:].sum(axis=1), totals[0], atol=1e-14)
    mask, directions = sphere_directions()
    values = scales[:,None]*harmonic_values(data['coefficients'], data['lm'], directions)
    assert np.max(abs(values)) <= .7
    fig = plt.figure(figsize=np.array([180,43])/25.4)
    cmap, norm = plt.colormaps['RdBu_r'], TwoSlopeNorm(vmin=-.7, vcenter=0, vmax=.7)
    for index, ((order,color),center) in enumerate(zip(MODELS,(.21,.395,.58))):
        fig.text(center,.13,f'{order}-body Hamiltonian',fontsize=8,ha='center',va='bottom')
        fig.add_artist(Line2D([center-.025,center+.025],[.22,.22],transform=fig.transFigure,color=color,lw=1.8))
        ax = fig.add_axes([center-.085,.25,.17,.17*180/43])
        rgba = np.zeros((*mask.shape,4)); rgba[mask] = cmap(norm(values[index]))
        ax.imshow(rgba,extent=(-1.01,1.01,-1.01,1.01),origin='lower',interpolation='bilinear')
        graticule(ax)
        ax.set(xlim=(-1.03,1.03),ylim=(-1.03,1.03)); ax.set_axis_off()
        if index == 0:
            field_rotation_cue(ax)
    color_ax = fig.add_axes([.082,.32,.008,.58])
    cb = fig.colorbar(plt.cm.ScalarMappable(norm=norm,cmap=cmap),cax=color_ax)
    cb.set_ticks([-.7,0,.7],labels=['−0.7','0','0.7'])
    cb.ax.tick_params(length=1.7,pad=1,labelsize=6.5)
    cb.ax.yaxis.set_ticks_position('left'); cb.ax.yaxis.set_label_position('left')
    cb.outline.set_linewidth(.45); cb.set_label('angular DSF',labelpad=3,fontsize=8)
    ax = fig.add_axes([.765,.24,.1875,.60])
    degrees = np.arange(1,6)
    for index, (_,color) in enumerate(MODELS):
        ax.bar(degrees+(index-1)*.30,amplitudes[index,1:6],width=.25,
               color=color,edgecolor='black',linewidth=.45,zorder=3)
    ax.set(xlim=(.5,5.5),ylim=(0,.35),xticks=degrees,yticks=[0,.1,.2,.3])
    ax.xaxis.set_minor_locator(NullLocator()); ax.yaxis.set_minor_locator(NullLocator())
    ax.tick_params(direction='out',length=3,width=.7,pad=2)
    ax.set_xlabel(r'$\ell$',labelpad=2)
    ax.set_ylabel(r'$A_\ell/J_\star$',labelpad=3,rotation=90,math_fontfamily='stix')
    for spine in ax.spines.values():
        spine.set_color('black'); spine.set_linewidth(.7)
    for extension in ('pdf','png'):
        fig.savefig(output/f'angular_main.{extension}',dpi=300,facecolor='white')
    plt.close(fig)
    rows = [dict(regime='ideal',family='honeycomb',body_order=order,temperature_over_B=0,
        ell=ell,A_over_J=float(amplitudes[i,ell]),unscaled_A_over_J=float(data['amplitudes'][i,ell]),
        hamiltonian_scale=float(scales[i])) for i,(order,_) in enumerate(MODELS) for ell in range(1,7)]
    return rows, dict(hamiltonian_scales=scales.tolist(),sum_A_over_J=float(totals[0]))


def thermal_coefficients(data):  # Fit smooth sphere images and check the independent angular grid.
    selected = np.flatnonzero(data['temperature_over_B'] == .1)
    assert len(selected) == 1
    selected = int(selected[0])
    directions = data['fine_directions']
    theta, phi = np.arccos(directions[:,2]), np.arctan2(directions[:,1],directions[:,0])
    coefficients, amplitudes, residuals = [], [], []
    for family in FAMILIES:
        signal = data[family+'_fine_signal'][:,selected]
        coeff, amp, lm = decompose(signal, theta, phi, data['fine_weights'], lmax=15)
        saved = data[family+'_fine_amplitudes'][:,selected]
        np.testing.assert_allclose(amp[:,:9],saved,atol=1e-12)
        residual = harmonic_values(coeff,lm,data['coarse_directions'])-data[family+'_coarse_signal'][:,selected]
        rms = np.sqrt(np.sum(data['coarse_weights']*residual**2,axis=-1)/(4*np.pi))
        assert np.max(rms) < 1e-4 and np.max(abs(residual)) < 5e-4
        residuals.append(dict(family=family,rms=rms.tolist(),maximum=float(np.max(abs(residual)))))
        coeff[:,0] = 0  # Remove the angular mean from sphere colors only.
        coefficients.append(coeff); amplitudes.append(saved)
    return np.asarray(coefficients), np.asarray(amplitudes), lm, residuals


def component_pdf(fig):  # Keep numerical components vector-based and in memory.
    stream = io.BytesIO()
    fig.savefig(stream,format='pdf',facecolor='white',dpi=500)
    plt.close(fig)
    return fitz.open(stream=stream.getvalue(),filetype='pdf')


def histogram(amplitude):  # Preserve absolute harmonic axes and all six displayed degrees.
    fig = plt.figure(figsize=(1.04,1.10))
    ax = fig.add_axes([.265/1.04,.38/1.10,.705/1.04,.49/1.10])
    ax.bar(np.arange(1,7),amplitude[1:7],width=.62,color='#bddced',linewidth=0,zorder=3)
    ax.set(xlim=(.45,6.55),ylim=(0,.60),xticks=np.arange(1,7),yticks=[0,.3,.6])
    ax.set_yticklabels(['0','0.3','0.6'])
    fig.text((.265+.705/2)/1.04,.105/1.10,r'$\ell$',ha='center',va='center',fontsize=8.4*1.30,color='#263746')
    fig.text(.265/1.04,1.015/1.10,r'$A_\ell/J$',ha='left',va='center',fontsize=8.2*1.30,color='#263746')
    ax.tick_params(labelsize=7.2*1.30,length=1.8,width=.45,pad=1.8,colors='#263746')
    ax.spines[['top','right']].set_visible(False)
    ax.spines['left'].set_color('#596875')
    ax.spines['bottom'].set_color('black'); ax.spines['bottom'].set_zorder(4)
    for edge in ('left','bottom'):
        ax.spines[edge].set_linewidth(.45)
    np.testing.assert_array_equal([bar.get_height() for bar in ax.patches],amplitude[1:7])
    return component_pdf(fig)


def color_scale(low, high):  # Match each sphere's individual zero-centered color scale.
    fig = plt.figure(figsize=(1.26,.54))
    ax = fig.add_axes([.13,.414/.54,.74,.0525/.54])
    norm = TwoSlopeNorm(vmin=low,vcenter=0,vmax=high)
    cb = fig.colorbar(plt.cm.ScalarMappable(norm=norm,cmap='RdBu_r'),cax=ax,
                     orientation='horizontal',ticks=[low,0,high])
    cb.ax.set_xticklabels([f'{low:.2f}','0',f'{high:.2f}']); cb.outline.set_visible(False)
    cb.ax.tick_params(labelsize=6.9*1.30,length=1.4,width=.4,pad=1.6,colors='#596875')
    fig.text(.5,.100/.54,r'$\Delta\mathcal{C}_{\mathbf{d}}/J$',ha='center',va='center',
             fontsize=7.6*1.30,color='#263746')
    return component_pdf(fig)


def supplement(data, data_dir, output, settings):  # Replace numerical panels within the original artwork.
    coefficients, amplitudes, lm, residuals = thermal_coefficients(data)
    mask, directions = sphere_directions(1.025)
    values = harmonic_values(coefficients,lm,directions)
    all_values = harmonic_values(coefficients,lm,angular_grid(64,128)[0])
    limits, components = [], {}
    with fitz.open(data_dir/'artwork.pdf') as artwork:
        for row, family in enumerate(STEMS):
            for i,(order,_) in enumerate(MODELS):
                low = np.floor(min(all_values[row,i].min(),values[row,i].min())*100)/100
                high = np.ceil(max(all_values[row,i].max(),values[row,i].max())*100)/100
                rgba = np.ones((*mask.shape,4)); rgba[~mask,3] = 0
                rgba[mask] = plt.colormaps['RdBu_r'](TwoSlopeNorm(vmin=low,vcenter=0,vmax=high)(values[row,i]))
                # Matplotlib's lower-origin images become PNG's top-first rows.
                stream = io.BytesIO()
                Image.fromarray(np.asarray(np.rint(255*rgba[::-1]),dtype=np.uint8)).save(stream,format='PNG')
                stem = f'{family}_individual_sphere_K{order}'
                doc = fitz.open(); doc.insert_pdf(artwork,from_page=settings['artwork_pages'][stem],to_page=settings['artwork_pages'][stem])
                images = {image[0] for image in doc[0].get_images(full=True)}
                assert len(images) == 1
                doc[0].replace_image(images.pop(),stream=stream.getvalue())
                components[stem] = doc
                components[f'{family}_histogram_K{order}'] = histogram(amplitudes[row,i])
                components[f'{family}_individual_scale_K{order}'] = color_scale(low,high)
                limits.append(dict(family=FAMILIES[row],body_order=order,minimum=float(low),maximum=float(high)))
        result = fitz.open()
        page = result.new_page(width=10.8*72,height=5.08*72)
        for stem,x,y,width,height in settings['layout']:
            document = components.get(stem,artwork)
            number = 0 if stem in components else settings['artwork_pages'][stem]
            page.show_pdf_page(fitz.Rect(x*72,y*72,(x+width)*72,(y+height)*72),document,number)
        result.save(output/'angular_supplement.pdf',garbage=4,deflate=True)
        page.get_pixmap(matrix=fitz.Matrix(300/72,300/72),alpha=False).save(output/'angular_supplement.png')
        result.close()
    for doc in components.values():
        doc.close()
    rows = [dict(regime='thermal',family=family,body_order=order,temperature_over_B=float(ratio),
        ell=ell,A_over_J=float(data[family+'_fine_amplitudes'][i,ti,ell]),
        unscaled_A_over_J=float(data[family+'_fine_amplitudes'][i,ti,ell]),hamiltonian_scale=1.)
        for family in FAMILIES for i,(order,_) in enumerate(MODELS)
        for ti,ratio in enumerate(data['temperature_over_B']) for ell in range(1,9)]
    return rows,dict(interpolation=residuals,color_limits=limits,displayed_temperature_over_B=.1)


def plot(data_dir, output_dir):  # Render both figures and export every harmonic value.
    data_dir, output = Path(data_dir), Path(output_dir)
    output.mkdir(parents=True,exist_ok=True)
    settings = json.loads((data_dir/'settings.json').read_text())
    with np.load(data_dir/'ideal.npz') as ideal, np.load(data_dir/'thermal.npz') as thermal:
        with plt.rc_context():
            main_rows, main_report = main_figure(ideal,output)
        with plt.rc_context({'font.family':'serif','font.serif':[fonts()['serif']],
                             'mathtext.fontset':'stix','pdf.fonttype':42,'savefig.bbox':None}):
            thermal_rows, thermal_report = supplement(thermal,data_dir,output,settings)
    with (output/'plotted.csv').open('w',newline='') as handle:
        writer = csv.DictWriter(handle,fieldnames=list(main_rows[0]))
        writer.writeheader(); writer.writerows(main_rows+thermal_rows)
    report = dict(fonts=fonts(),ideal=main_report,thermal=thermal_report)
    (output/'render.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():  # Choose a figure or data check.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['plot', 'check'])
    parser.add_argument('--data-dir', type=Path, default=DATA)
    parser.add_argument('--output', type=Path, default=RUNS/'figures')
    parser.add_argument('--physics', action='store_true', help='check six fresh N=12 traces')
    args = parser.parse_args()
    if args.command == 'plot':
        plot(args.data_dir, args.output)
    else:
        check(args.data_dir, args.physics)


if __name__ == '__main__':
    main()
