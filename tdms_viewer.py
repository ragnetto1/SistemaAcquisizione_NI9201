import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter import ttk
import numpy as np
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.patches import Circle
from nptdms import TdmsFile

class TDMSViewerSamples(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("TDMS Channel Viewer (asse X = samples)")
        self.geometry("1150x700")

        self.tdms = None
        self.channels = []   # (group_name, channel_name, channel_obj)
        self.x = None        # sample index
        self.y = None        # data

        self._build_ui()
        self._connect_matplotlib_events()

    # ---------------- UI ----------------
    def _build_ui(self):
        left = ttk.Frame(self)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=8, pady=8)

        ttk.Button(left, text="Apri TDMS…", command=self.open_tdms).pack(fill=tk.X, pady=(0, 8))

        self.tree = ttk.Treeview(left, columns=("type",), show="tree", height=25)
        self.tree.pack(fill=tk.BOTH, expand=True)

        ttk.Button(left, text="Disegna canale selezionato", command=self.plot_selected)\
            .pack(fill=tk.X, pady=(8, 0))

        right = ttk.Frame(self)
        right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=8, pady=8)

        self.fig, self.ax = plt.subplots()
        self.fig.set_tight_layout(True)
        self.canvas = FigureCanvasTkAgg(self.fig, master=right)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        self.toolbar = NavigationToolbar2Tk(self.canvas, right)
        self.toolbar.update()

        # Annotazioni
        self.max_ann = None
        self.min_ann = None
        self.max_circle = None
        self.min_circle = None
        self.info_text = None

    def _connect_matplotlib_events(self):
        self.ax.callbacks.connect("xlim_changed", self._on_view_change)
        self.ax.callbacks.connect("ylim_changed", self._on_view_change)
        self.canvas.mpl_connect("draw_event", self._on_draw_event)

    # ---------------- TDMS ----------------
    def open_tdms(self):
        path = filedialog.askopenfilename(
            title="Seleziona un file TDMS",
            filetypes=[("TDMS files", "*.tdms"), ("Tutti i file", "*.*")]
        )
        if not path:
            return
        try:
            self.tdms = TdmsFile.read(path)
        except Exception as e:
            messagebox.showerror("Errore apertura TDMS", str(e))
            return

        self.channels.clear()
        self.tree.delete(*self.tree.get_children())
        group_nodes = {}

        for group in self.tdms.groups():
            if group.name not in group_nodes:
                group_nodes[group.name] = self.tree.insert("", "end", text=group.name, open=True)
            for ch in group.channels():
                self.channels.append((group.name, ch.name, ch))
                self.tree.insert(group_nodes[group.name], "end", text=ch.name, values=("channel",))

        messagebox.showinfo("TDMS caricato", f"Trovati {len(self.channels)} canali.")

    def _get_selected_channel(self):
        sel = self.tree.selection()
        if not sel:
            return None
        node = sel[0]
        parent = self.tree.parent(node)
        if not parent:  # hanno cliccato un gruppo
            return None
        gname = self.tree.item(parent, "text")
        cname = self.tree.item(node, "text")
        for G, C, ch in self.channels:
            if G == gname and C == cname:
                return ch
        return None

    # ---------------- Plot & annotazioni ----------------
    def plot_selected(self):
        ch = self._get_selected_channel()
        if ch is None:
            messagebox.showwarning("Seleziona canale", "Seleziona un canale dal pannello a sinistra.")
            return

        try:
            y = ch[:]
        except Exception as e:
            messagebox.showerror("Errore lettura canale", str(e))
            return

        if not isinstance(y, np.ndarray):
            y = np.array(y, dtype=float)
        else:
            y = y.astype(float, copy=False)

        # Filtra NaN/Inf
        finite_mask = np.isfinite(y)
        if not finite_mask.all():
            y = y[finite_mask]
        if y.size == 0:
            messagebox.showwarning("Canale vuoto", "Il canale non contiene dati numerici validi.")
            return

        self.y = y
        self.x = np.arange(y.size, dtype=float)

        # Reset grafico
        self.ax.clear()
        self._clear_annotations()

        self.ax.plot(self.x, self.y, "-", lw=1)
        self.ax.set_xlabel("Indice campione")
        self.ax.set_ylabel("Ampiezza")
        self.ax.grid(True, alpha=0.3)

        # Annotazioni iniziali su tutto il range
        self._update_annotations()
        self.canvas.draw_idle()

    def _on_view_change(self, _axis):
        if self.x is None:
            return
        self._update_annotations()
        self.canvas.draw_idle()

    def _on_draw_event(self, _event):
        if self.x is None:
            return
        self._update_annotations()

    def _clear_annotations(self):
        for artist in [self.max_ann, self.min_ann, self.max_circle, self.min_circle, self.info_text]:
            if artist is not None:
                try:
                    artist.remove()
                except Exception:
                    pass
        self.max_ann = self.min_ann = self.max_circle = self.min_circle = self.info_text = None

    def _update_annotations(self):
        if self.x is None:
            return

        xlim = self.ax.get_xlim()
        ylim = self.ax.get_ylim()
        x = self.x
        y = self.y

        # Punti visibili
        visible = (x >= min(xlim)) & (x <= max(xlim))
        if not np.any(visible):
            self._clear_annotations()
            return

        xv = x[visible]
        yv = y[visible]
        if xv.size == 0:
            self._clear_annotations()
            return

        idx_local_max = np.nanargmax(yv)
        idx_local_min = np.nanargmin(yv)
        x_max, y_max = xv[idx_local_max], yv[idx_local_max]
        x_min, y_min = xv[idx_local_min], yv[idx_local_min]

        self._clear_annotations()

        # Cerchi
        r = 0.01 * (xlim[1] - xlim[0]) if xlim[1] > xlim[0] else 1.0
        self.max_circle = Circle((x_max, y_max), radius=r, fill=False, lw=2)
        self.min_circle = Circle((x_min, y_min), radius=r, fill=False, lw=2)
        self.ax.add_patch(self.max_circle)
        self.ax.add_patch(self.min_circle)

        # Frecce + etichette
        self.max_ann = self.ax.annotate(
            f"MAX: y={y_max:.6g} @ n={int(round(x_max))}",
            xy=(x_max, y_max),
            xytext=(20, 20),
            textcoords="offset points",
            arrowprops=dict(arrowstyle="->"),
            fontsize=9, bbox=dict(boxstyle="round,pad=0.2", fc="w", alpha=0.85)
        )
        self.min_ann = self.ax.annotate(
            f"MIN: y={y_min:.6g} @ n={int(round(x_min))}",
            xy=(x_min, y_min),
            xytext=(-40, -30),
            textcoords="offset points",
            arrowprops=dict(arrowstyle="->"),
            fontsize=9, bbox=dict(boxstyle="round,pad=0.2", fc="w", alpha=0.85)
        )

        # Flag riassuntivo finestra
        yv_min = np.nanmin(yv)
        yv_max = np.nanmax(yv)
        info = (f"Finestra visibile:\n"
                f"n ∈ [{int(np.floor(xv.min()))} , {int(np.ceil(xv.max()))}]\n"
                f"y ∈ [{yv_min:.6g} , {yv_max:.6g}]\n"
                f"Max visibile: {y_max:.6g} (n={int(round(x_max))})\n"
                f"Min visibile: {y_min:.6g} (n={int(round(x_min))})")
        self.info_text = self.ax.text(
            0.02, 0.98, info, transform=self.ax.transAxes,
            va="top", ha="left", fontsize=9,
            bbox=dict(boxstyle="round,pad=0.3", fc="w", alpha=0.85)
        )

        # Mantieni limiti
        self.ax.set_xlim(xlim)
        self.ax.set_ylim(ylim)

if __name__ == "__main__":
    app = TDMSViewerSamples()
    app.mainloop()
