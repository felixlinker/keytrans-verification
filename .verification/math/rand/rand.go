package rand

type Source interface{}

type Rand struct{}

func NewSource(seed int64) Source
func New(source Source) *Rand

func (r *Rand) Read(p []byte) (n int, err error)
func (r *Rand) Intn(n int) int
func (r *Rand) Perm(n int) []int
